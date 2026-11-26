// discrete.go — the nonnegative integral against the discrete measure of
// weights w: the supremum, over the finite subsets of the points, of the
// weighted sums of the values.

package integral_convergence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_simple"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// DiscreteNonnegIntegral — the integral for the discrete measure of weights
// w is the weighted sum: the supremum, over the finite subsets of J, of the
// sums of w(i)·f(i). Every function is measurable for the subsets of J. For
// a simple s, y times the discrete measure of the level set {s = y} is the
// discrete measure there of the weights w·s, s being y on it (SupScale); the
// level sets partition J, so the simple integral is the discrete measure of
// J for w·s. A function f is the supremum of a rising sequence of simple
// s(n), so its integral is the supremum of their simple integrals; and its
// weighted sum is the supremum of the weighted sums of the s(n), w(i) moving
// through the supremum of the s(n, i) (SupSequenceScaleExtended) and each
// finite sum through the supremum of its rising terms (SupSequenceSum).
var DiscreteNonnegIntegral = discreteNonnegIntegralThm{family.Add(registry.ProofEntry{
	Name:    "DiscreteNonnegIntegral",
	Reading: "It holds with infinite weights or values, since 0·∞ = 0 on both sides.",
	Key:     "prop_f7e9551a8345db7",
	Build: family.Sections(Statement{
		Binders: "∀J:set(I). ∀w f:(I → extended_nonneg_real).",
		Conclusion: "nonneg_integral(J, {E:set(I) | E ⊆ J}, discrete_measure(J, w), f) = " +
			"discrete_measure(J, λi:I. w(i) * f(i), J)",
		Abbrev: Abbrev{
			{Name: "subsets", Text: "{E:set(I) | E ⊆ J}"},
			{Name: "sums", Text: "λv:(I → extended_nonneg_real). λU:set(I). " +
				"    {r:extended_nonneg_real | ∃F:set(I). finite(F) ∧ F ⊆ J ∩ U ∧ r = Σ_{i∈F} v(i)}"},
			{Name: "level", Text: "λg:(I → real). λy:real. {x:I | x ∈ J ∧ g(x) = y}"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		simpleCase := ctx.Lemma(Statement{
			Binders:    "∀J:set(I). ∀w:(I → extended_nonneg_real). ∀s:(I → real).",
			Hypotheses: []string{"measure_simple(J, «subsets», s)"},
			Conclusion: "measure_simple_integral(J, discrete_measure(J, w), s) = " +
				"discrete_measure(J, λi:I. w(i) * extended_of_real(s(i)), J)",
		}, func(
			arg *Argument,
			J *Expr[Set[I]],
			w *Arrow[I, ExtendedNonnegReal],
			s *Arrow[I, Real],
			simple Fact,
		) {
			parts := arg.Conjuncts(
				arg.Unfolded(simple, measure_simple.NonnegSimpleDef),
				"s is measurable",
				"s takes finitely many values on J",
				"s is nonnegative on J")
			weights := arg.TermAs[Fun[I, ExtendedNonnegReal]]("λi:I. w(i) * extended_of_real(s(i))")
			scaled := arg.Have(
				"on each level set, y times the discrete measure for w is the discrete measure for w·s",
				Statement{
					Binders:    "∀y:real.",
					Hypotheses: []string{"y ∈ image(s, J)"},
					Conclusion: "extended_of_real(y) * discrete_measure(J, w, «level»(s, y)) = " +
						"discrete_measure(J, λi:I. w(i) * extended_of_real(s(i)), «level»(s, y))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Real]("y")
					level := b.TermAs[Set[I]]("«level»(s, y)")
					sumEach := b.Have(
						"over a finite subset F of the level set, y times the sum of w is the sum of w·s, s being y on F",
						Statement{
							Binders:    "∀F:set(I).",
							Hypotheses: []string{"finite(F)", "F ⊆ J ∩ «level»(s, y)"},
							Conclusion: "extended_of_real(y) * Σ_{i∈F} w(i) = Σ_{i∈F} w(i) * extended_of_real(s(i))",
						},
						Derive(func(c *Argument) {
							F := c.FixAs[Set[I]]("F")
							given := c.Conjuncts(
								c.Assume(),
								"F is finite",
								"F lies in the level set")
							termwise := c.Have(
								"on F each term y·w(i) is w(i)·s(i)",
								"∀i:I. i ∈ F ⇒ extended_of_real(y) * w(i) = w(i) * extended_of_real(s(i))",
								BySets(given[1], extended_nonneg_real.MulComm))
							c.Show(
								"move y into the sum, then match the terms",
								By(
									given[0],
									extended_nonneg_real.SumScale.At(b.TermAs[ExtendedNonnegReal]("extended_of_real(y)"), w, F),
									termwise,
									monoidal.Congruence.Read(extended_nonneg_real.MonoidalAdd).At(
										F,
										c.TermAs[Fun[I, ExtendedNonnegReal]]("λi:I. extended_of_real(y) * w(i)"),
										c.TermAs[Fun[I, ExtendedNonnegReal]]("λi:I. w(i) * extended_of_real(s(i))")),
									extended_nonneg_real.ExtendedSumDef))
						}))
					images := b.Have(
						"so scaling the sums of w by y gives the sums of w·s over the level set",
						"image(λx:extended_nonneg_real. extended_of_real(y) * x, «sums»(w, «level»(s, y))) = "+
							"«sums»(λi:I. w(i) * extended_of_real(s(i)), «level»(s, y))",
						Derive(func(c *Argument) {
							same := c.Have(
								"a value is one exactly when it is the other",
								"∀r:extended_nonneg_real. "+
									"    r ∈ image(λx:extended_nonneg_real. extended_of_real(y) * x, «sums»(w, «level»(s, y))) ⇔ "+
									"    r ∈ «sums»(λi:I. w(i) * extended_of_real(s(i)), «level»(s, y))",
								Derive(func(d *Argument) {
									d.FixAs[ExtendedNonnegReal]("r")
									d.Iff()
									d.Forward(
										"y times the sum of w over F is the sum of w·s over F",
										func(e *Argument, scaledSum Fact) {
											_, parts := e.UnpackAs[ExtendedNonnegReal](e.Simplified(scaledSum, Fwd(set_basic.InImage)), "x")
											pieces := e.Conjuncts(
												parts,
												"r is y times x",
												"x is a sum of w over a finite subset of the level set")
											F, member := e.UnpackAs[Set[I]](pieces[1], "F")
											facts := e.Conjuncts(
												member,
												"F is finite",
												"F lies in the level set",
												"x is the sum over F")
											e.Show(
												"so r is the sum of w·s over F",
												By(pieces[0], facts[0], facts[1], facts[2], sumEach.At(F)))
										})
									d.Backward(
										"the sum of w·s over F is y times the sum of w over F",
										func(e *Argument, sum Fact) {
											F, member := e.UnpackAs[Set[I]](sum, "F")
											facts := e.Conjuncts(
												member,
												"F is finite",
												"F lies in the level set",
												"r is the sum over F")
											e.Show(
												"so r is y times a sum of w",
												By(facts[0], facts[1], facts[2], sumEach.At(F), set_basic.InImage))
										})
								}))
							c.Show(
								"sets with the same members are equal",
								BySets(same))
						}))
					b.Show(
						"and y moves through the supremum",
						By(
							images,
							measure_space.DiscreteMeasureDef.At(J, w, level),
							measure_space.DiscreteMeasureDef.At(J, weights, level),
							extended_nonneg_real.SupScale.At(
								b.TermAs[ExtendedNonnegReal]("extended_of_real(y)"),
								b.TermAs[Set[ExtendedNonnegReal]]("«sums»(w, «level»(s, y))"))))
				}))
			regrouped := arg.Have(
				"so the simple integral is the sum over the values of "+
					"s of the discrete measures of the level sets for w·s",
				"measure_simple_integral(J, discrete_measure(J, w), s) = "+
					"Σ_{y∈image(s, J)} discrete_measure(J, λi:I. w(i) * extended_of_real(s(i)), «level»(s, y))",
				Derive(func(b *Argument) {
					b.Do(Unfold(measure_simple.SimpleIntegralDef))
					b.Show(
						"the terms agree value by value",
						By(
							scaled,
							monoidal.Congruence.Read(extended_nonneg_real.MonoidalAdd).At(
								b.TermAs[Set[Real]]("image(s, J)"),
								b.TermAs[Fun[Real, ExtendedNonnegReal]](
									"λy:real. extended_of_real(y) * discrete_measure(J, w, «level»(s, y))"),
								b.TermAs[Fun[Real, ExtendedNonnegReal]](
									"λy:real. discrete_measure(J, λi:I. w(i) * extended_of_real(s(i)), «level»(s, y))")),
							extended_nonneg_real.ExtendedSumDef))
				}))
			additive := arg.Have(
				"the level sets partition J, so their discrete measures for w·s add up to that of J",
				"Σ_{y∈image(s, J)} discrete_measure(J, λi:I. w(i) * extended_of_real(s(i)), «level»(s, y)) = "+
					"discrete_measure(J, λi:I. w(i) * extended_of_real(s(i)), J)",
				Derive(func(b *Argument) {
					cover := b.Have(
						"the level sets of the values of s on J make up J",
						"⋃image(λy:real. «level»(s, y), image(s, J)) = J",
						BySets())
					pieces := b.Have(
						"each level set is a subset of J, and distinct ones are disjoint",
						"(∀y:real. y ∈ image(s, J) ⇒ «level»(s, y) ∈ «subsets») ∧ "+
							"(∀y z:real. y ∈ image(s, J) ∧ z ∈ image(s, J) ∧ y ≠ z ⇒ disjoint(«level»(s, y), «level»(s, z)))",
						BySets())
					b.Show(
						"finite additivity of the discrete measure for w·s",
						By(
							cover,
							pieces,
							parts[1],
							measure_space.DiscreteMeasure.At(J, weights),
							measure_space.MeasureFiniteAdditive.At(
								J,
								b.TermAs[Set[Set[I]]]("«subsets»"),
								b.TermAs[Fun[Set[I], ExtendedNonnegReal]](
									"discrete_measure(J, λi:I. w(i) * extended_of_real(s(i)))"),
								b.TermAs[Fun[Real, Set[I]]]("λy:real. «level»(s, y)"),
								b.TermAs[Set[Real]]("image(s, J)"))))
				}))
			arg.Show(
				"the two steps chain",
				By(regrouped, additive))
		})
		weightLimit := ctx.Lemma(Statement{
			Binders: "∀J:set(I). ∀w f:(I → extended_nonneg_real). ∀s:(num → I → real).",
			Hypotheses: []string{
				"∀n:num. ∀x:I. x ∈ J ⇒ &0 ≤ s(n, x)",
				"∀n:num. ∀x:I. x ∈ J ⇒ s(n, x) ≤ s(n + 1, x)",
				"∀x:I. x ∈ J ⇒ f(x) = extended_sup(image(λn:num. extended_of_real(s(n, x)), 𝕌))",
			},
			Conclusion: "discrete_measure(J, λi:I. w(i) * f(i), J) = " +
				"extended_sup(image(λn:num. discrete_measure(J, λi:I. w(i) * extended_of_real(s(n, i)), J), 𝕌))",
		}, func(arg *Argument, J *Expr[Set[I]], w, f *Arrow[I, ExtendedNonnegReal], s *Arrow2[Nat, I, Real],
			nonneg, rising, limit Fact) {
			whole := arg.TermAs[ExtendedNonnegReal]("discrete_measure(J, λi:I. w(i) * f(i), J)")
			partials := arg.TermAs[Fun[Nat, ExtendedNonnegReal]](
				"λn:num. discrete_measure(J, λi:I. w(i) * extended_of_real(s(n, i)), J)")
			supPartials := arg.TermAs[ExtendedNonnegReal](
				"extended_sup(image(λn:num. discrete_measure(J, λi:I. w(i) * extended_of_real(s(n, i)), J), 𝕌))")
			fWeights := arg.TermAs[Fun[I, ExtendedNonnegReal]]("λi:I. w(i) * f(i)")
			below := arg.Have(
				"each weighted sum for s(n) is at most that for f, s(n) lying below f",
				"∀n:num. "+
					"    discrete_measure(J, λi:I. w(i) * extended_of_real(s(n, i)), J) ≤ "+
					"    discrete_measure(J, λi:I. w(i) * f(i), J)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					under := b.Have(
						"on J, w·s(n) lies below w·f",
						"∀i:I. i ∈ J ⇒ w(i) * extended_of_real(s(n, i)) ≤ w(i) * f(i)",
						Derive(func(c *Argument) {
							i := c.FixAs[I]("i")
							inJ := c.Assume()
							term := c.TermAs[ExtendedNonnegReal]("extended_of_real(s(n, i))")
							c.Show(
								"s(n, i) lies below the supremum f(i), and so after the weight",
								By(
									inJ,
									limit.At(i),
									extended_nonneg_real.SupSequenceUpper.At(
										c.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. extended_of_real(s(n, i))"),
										n),
									extended_nonneg_real.MulLeMono.At(term, f.Apply(i), w.Apply(i))))
						}))
					nWeights := b.TermAs[Fun[I, ExtendedNonnegReal]]("λi:I. w(i) * extended_of_real(s(n, i))")
					each := b.Have(
						"so each sum for s(n) is at most a sum for f, and so at most the weighted sum for f",
						Statement{
							Binders:    "∀r:extended_nonneg_real.",
							Hypotheses: []string{"r ∈ «sums»(λi:I. w(i) * extended_of_real(s(n, i)), J)"},
							Conclusion: "r ≤ discrete_measure(J, λi:I. w(i) * f(i), J)",
						},
						Derive(func(c *Argument) {
							c.FixAs[ExtendedNonnegReal]("r")
							F, member := c.UnpackAs[Set[I]](c.Assume(), "F")
							parts := c.Conjuncts(
								member,
								"F is finite",
								"F lies in J",
								"r is the sum over F")
							termsBelow := c.Have(
								"on F, w·s(n) lies below w·f",
								"∀i:I. i ∈ F ⇒ w(i) * extended_of_real(s(n, i)) ≤ w(i) * f(i)",
								BySets(parts[1], under))
							c.Show(
								"the sum over F for f is among those for f",
								By(
									parts[2],
									parts[0],
									parts[1],
									termsBelow,
									extended_nonneg_real.SumMono.At(nWeights, fWeights, F),
									measure_space.DiscreteMeasureDef.At(J, fWeights, J),
									extended_nonneg_real.SupUpper,
									extended_nonneg_real.LeTrans))
						}))
					b.Show(
						"a bound of the sums bounds their supremum",
						By(measure_space.DiscreteMeasureDef.At(J, nWeights, J), each, extended_nonneg_real.SupLeast))
				}))
			above := arg.Have(
				"the weighted sum for f is at most the supremum of those for the s(n)",
				"discrete_measure(J, λi:I. w(i) * f(i), J) ≤ "+
					"extended_sup(image(λn:num. discrete_measure(J, λi:I. w(i) * extended_of_real(s(n, i)), J), 𝕌))",
				Derive(func(b *Argument) {
					each := b.Have(
						"each sum over a finite F for f is the supremum of the sums over F for the s(n)",
						Statement{
							Binders:    "∀r:extended_nonneg_real.",
							Hypotheses: []string{"r ∈ «sums»(λi:I. w(i) * f(i), J)"},
							Conclusion: "r ≤ " +
								"extended_sup(image(λn:num. discrete_measure(J, λi:I. w(i) * extended_of_real(s(n, i)), J), 𝕌))",
						},
						Derive(func(c *Argument) {
							c.FixAs[ExtendedNonnegReal]("r")
							F, member := c.UnpackAs[Set[I]](c.Assume(), "F")
							parts := c.Conjuncts(
								member,
								"F is finite",
								"F lies in J",
								"r is the sum over F")
							raised := c.Have(
								"on F, w(i)·f(i) is the supremum of the w(i)·s(n, i)",
								"∀i:I. i ∈ F ⇒ w(i) * f(i) = extended_sup(image(λn:num. w(i) * extended_of_real(s(n, i)), 𝕌))",
								Derive(func(d *Argument) {
									i := d.FixAs[I]("i")
									inF := d.Assume()
									inJ := d.Have(
										"i lies in J",
										"i ∈ J",
										BySets(inF, parts[1]))
									d.Show(
										"f(i) is the supremum of the s(n, i), and w(i) moves through it",
										By(
											inJ,
											limit.At(i),
											extended_nonneg_real.SupSequenceScaleExtended.At(
												w.Apply(i),
												d.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. extended_of_real(s(n, i))"))))
								}))
							climbing := c.Have(
								"on F the w(i)·s(n, i) rise with n",
								"∀i:I. ∀n:num. i ∈ F ⇒ w(i) * extended_of_real(s(n, i)) ≤ w(i) * extended_of_real(s(n + 1, i))",
								Derive(func(d *Argument) {
									i := d.FixAs[I]("i")
									n := d.FixAs[Nat]("n")
									inF := d.Assume()
									inJ := d.Have(
										"i lies in J",
										"i ∈ J",
										BySets(inF, parts[1]))
									next := d.TermAs[Nat]("n + 1")
									d.Show(
										"s rises at i and stays nonnegative, so its image rises, and so does the weighted term",
										By(
											inJ,
											rising.At(n, i),
											nonneg.At(next, i),
											extended_nonneg_real.OfRealLe,
											extended_nonneg_real.MulLeMono.At(
												d.TermAs[ExtendedNonnegReal]("extended_of_real(s(n, i))"),
												d.TermAs[ExtendedNonnegReal]("extended_of_real(s(n + 1, i))"),
												w.Apply(i))))
								}))
							summed := c.Have(
								"so the sum over F for f is the supremum of the sums over F for the s(n)",
								"Σ_{i∈F} w(i) * f(i) = extended_sup(image(λn:num. Σ_{i∈F} w(i) * extended_of_real(s(n, i)), 𝕌))",
								By(
									parts[0],
									raised,
									climbing,
									monoidal.Congruence.Read(extended_nonneg_real.MonoidalAdd).At(
										F,
										c.TermAs[Fun[I, ExtendedNonnegReal]]("λi:I. w(i) * f(i)"),
										c.TermAs[Fun[I, ExtendedNonnegReal]](
											"λi:I. extended_sup(image(λn:num. w(i) * extended_of_real(s(n, i)), 𝕌))")),
									extended_nonneg_real.ExtendedSumDef,
									extended_nonneg_real.SupSequenceSum.At(
										c.TermAs[Fun[I, Fun[Nat, ExtendedNonnegReal]]]("λi:I. λn:num. w(i) * extended_of_real(s(n, i))"),
										F)))
							bounded := c.Have(
								"each sum over F for s(n) is at most the weighted sum for s(n), and so at most their supremum",
								"∀n:num. "+
									"    Σ_{i∈F} w(i) * extended_of_real(s(n, i)) ≤ "+
									"    extended_sup( "+
									"        image(λn:num. discrete_measure(J, λi:I. w(i) * extended_of_real(s(n, i)), J), 𝕌))",
								Derive(func(d *Argument) {
									n := d.FixAs[Nat]("n")
									nWeights := d.TermAs[Fun[I, ExtendedNonnegReal]]("λi:I. w(i) * extended_of_real(s(n, i))")
									d.Show(
										"it is among the sums for s(n)",
										By(
											parts[0],
											parts[1],
											measure_space.DiscreteMeasureDef.At(J, nWeights, J),
											extended_nonneg_real.SupUpper.At(
												d.TermAs[Set[ExtendedNonnegReal]]("«sums»(λi:I. w(i) * extended_of_real(s(n, i)), J)"),
												d.TermAs[ExtendedNonnegReal]("Σ_{i∈F} w(i) * extended_of_real(s(n, i))")),
											extended_nonneg_real.SupSequenceUpper.At(partials, n),
											extended_nonneg_real.LeTrans))
								}))
							sumsOverF := c.TermAs[Fun[Nat, ExtendedNonnegReal]](
								"λn:num. Σ_{i∈F} w(i) * extended_of_real(s(n, i))")
							c.Show(
								"so r is at most the supremum of the weighted sums for the s(n)",
								By(parts[2], summed, bounded, extended_nonneg_real.SupSequenceLeast.At(sumsOverF, supPartials)))
						}))
					b.Show(
						"a bound of the sums bounds their supremum",
						By(measure_space.DiscreteMeasureDef.At(J, fWeights, J), each, extended_nonneg_real.SupLeast))
				}))
			arg.Show(
				"each side lies below the other",
				By(
					above,
					below,
					extended_nonneg_real.SupSequenceLeast.At(partials, whole),
					extended_nonneg_real.LeAntisym))
		})
		return ctx.Theorem(headline, func(
			arg *Argument,
			J *Expr[Set[I]],
			w, f *Arrow[I, ExtendedNonnegReal],
		) {
			subsets := arg.TermAs[Set[Set[I]]]("«subsets»")
			measure := arg.Have(
				"the discrete measure is a measure on the subsets of J",
				"measure_on(J, «subsets», discrete_measure(J, w))",
				By(measure_space.DiscreteMeasure.At(J, w)))
			sigma := arg.Conjuncts(
				arg.Unfolded(measure, measure_space.MeasureOn),
				"the subsets of J form a sigma algebra",
				"the empty set has measure zero",
				"countable disjoint unions have the series of their measures")[0]
			rays := arg.Have(
				"every ray of f is a subset of J",
				"∀r:real. {x:I | x ∈ J ∧ extended_of_real(r) < f(x)} ∈ «subsets»",
				BySets())
			measurable := arg.Have(
				"so f is measurable for the subsets of J",
				"extended_measurable(J, «subsets», f)",
				By(sigma, rays, measurable_function.ExtendedMeasurableIffRay.At(J, subsets, f)))
			s, approximation := arg.ObtainAs[Fun2[Nat, I, Real]](
				"a rising sequence of simple functions s(n) has supremum f",
				"∃s:(num → I → real). "+
					"    (∀n:num. measure_simple(J, «subsets», s(n))) ∧ "+
					"    (∀n:num. ∀x:I. x ∈ J ⇒ s(n, x) ≤ s(n + 1, x)) ∧ "+
					"    (∀n:num. ∀x:I. x ∈ J ⇒ extended_of_real(s(n, x)) ≤ f(x)) ∧ "+
					"    (∀x:I. x ∈ J ⇒ f(x) = extended_sup(image(λn:num. extended_of_real(s(n, x)), 𝕌)))",
				By(sigma, measurable, measure_simple.SimpleApproximation.At(J, subsets, f)))
			parts := arg.Conjuncts(
				approximation,
				"each s(n) is simple",
				"the s(n) rise",
				"each s(n) lies below f",
				"f is their supremum")
			integral := arg.Have(
				"so the integral of f is the supremum of the simple integrals of the s(n)",
				"nonneg_integral(J, «subsets», discrete_measure(J, w), f) = "+
					"extended_sup(image(λn:num. measure_simple_integral(J, discrete_measure(J, w), s(n)), 𝕌))",
				By(
					measure,
					parts[0],
					parts[1],
					parts[3],
					nonneg_integral.MonotoneConvergenceSimple.At(
						J,
						subsets,
						arg.TermAs[Fun[Set[I], ExtendedNonnegReal]]("discrete_measure(J, w)"),
						s,
						f)))
			simpleIntegrals := arg.Have(
				"each simple integral is the weighted sum for s(n)",
				"∀n:num. "+
					"    measure_simple_integral(J, discrete_measure(J, w), s(n)) = "+
					"    discrete_measure(J, λi:I. w(i) * extended_of_real(s(n, i)), J)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					b.Show(
						"the simple case",
						By(parts[0], At(simpleCase, J, w, b.TermAs[Fun[I, Real]]("s(n)"))))
				}))
			nonneg := arg.Have(
				"each s(n) is nonnegative on J",
				"∀n:num. ∀x:I. x ∈ J ⇒ &0 ≤ s(n, x)",
				By(parts[0], measure_simple.NonnegSimpleDef))
			arg.Show(
				"and the weighted sum for f is the supremum of those for the s(n)",
				By(
					arg.Simplified(integral, Fwd(simpleIntegrals)),
					nonneg,
					parts[1],
					parts[3],
					At(weightLimit, J, w, f, s)))
		})
	}),
})}

// FiniteDiscreteIntegral — on a finite carrier the discrete measure of
// nonnegative real weights integrates every real function, to its weighted sum.
var FiniteDiscreteIntegral = finiteDiscreteIntegralThm{family.Add(registry.ProofEntry{
	Name:    "FiniteDiscreteIntegral",
	Key:     "prop_ec7b004a915a4667",
	Reading: "Nonnegative weights are load-bearing: extended_of_real clamps a negative weight to zero.",
	Deps: []registry.EntryLike{
		DiscreteNonnegIntegral,
		measure_integral.RealIntegrableDef,
		measure_integral.RealIntegralDef,
	},
	Build: family.Card(Statement{
		Binders:    "∀J:set(I). ∀w f:(I → real).",
		Hypotheses: []string{"finite(J)", "∀i:I. i ∈ J ⇒ &0 ≤ w(i)"},
		Conclusion: "real_integrable(J, " +
			"    {E:set(I) | E ⊆ J}, " +
			"    discrete_measure(J, λi:I. extended_of_real(w(i))), " +
			"    f) ∧ " +
			"measure_integral(J, {E:set(I) | E ⊆ J}, discrete_measure(J, λi:I. extended_of_real(w(i))), f) = " +
			"real_sum(J, λi:I. w(i) * f(i))",
	},
		"Every function is measurable for the subsets of J. DiscreteNonnegIntegral reads the "+
			"integrals of the embedded positive and negative parts of f as the weighted sums of max(f, "+
			"0) and max(−f, 0), both finite on a finite J; their difference is the weighted sum of f."),
})}
