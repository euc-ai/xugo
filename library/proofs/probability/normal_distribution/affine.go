package normal_distribution

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/borel_function"
	"github.com/euc-ai/xugo/library/proofs/measure/density_measure"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/probability/random_variable"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_riemann"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// NormalDistributionAffine — under the normal law of mean m and variance v a
// Borel h has the integrability and the expectation that h(m + √v·y) has
// under the standard law. The proof shows the normal law is the image of the
// standard one under y ↦ m + √v·y: the two give each lower ray the same mass,
// the supremum of the masses of closed windows, which the substitution
// x = m + √v·y carries across, and a Borel probability on the line is
// determined by the masses of its lower rays.
var NormalDistributionAffine = normalDistributionAffineThm{family.Add(registry.ProofEntry{
	Name: "NormalDistributionAffine",
	Key:  "prop_2cd76f5ddf3937f6",
	Reading: "The equality of the expectations holds without integrability, each side " +
		"reading the same positive and negative parts. real_sqrt(v) is the standard deviation.",
	Build: family.Sections(Statement{
		Binders: "∀m v:real. ∀h:(real → real).",
		Hypotheses: []string{
			"&0 < v",
			"real_measurable(𝕌, borel_sets(real_topology), h)",
		},
		Conclusion: "(real_integrable(𝕌, borel_sets(real_topology), normal_distribution(m, v), h) ⇔ " +
			"    real_integrable(𝕌, " +
			"        borel_sets(real_topology), " +
			"        normal_distribution(&0, &1), " +
			"        λy:real. h(m + real_sqrt(v) * y))) ∧ " +
			"expectation(𝕌, borel_sets(real_topology), normal_distribution(m, v), h) = " +
			"expectation(𝕌, " +
			"    borel_sets(real_topology), " +
			"    normal_distribution(&0, &1), " +
			"    λy:real. h(m + real_sqrt(v) * y))",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			affineMapMeasurable := ctx.Lemma("∀m s:real. "+
				"    measurable_map(𝕌, "+
				"        borel_sets(real_topology), "+
				"        𝕌, "+
				"        borel_sets(real_topology), "+
				"        λx:real. m + s * x)",
				func(a *Argument, m, s *Expr[Real]) {
					line := a.TermAs[Set[Real]]("𝕌")
					affine := a.TermAs[Fun[Real, Real]]("λx:real. m + s * x")
					continuous := a.Have(
						"the affine map is continuous on the line: a constant plus a constant times the identity",
						"real_continuous_on(𝕌, λx:real. m + s * x)",
						By(
							real_continuous.ContinuousOnId.At(line),
							real_continuous.ContinuousOnConst.At(m, line),
							real_continuous.ContinuousOnConst.At(s, line),
							real_continuous.ContinuousOnMul.At(
								a.TermAs[Fun[Real, Real]]("λx:real. s"), a.TermAs[Fun[Real, Real]]("λx:real. x"), line),
							real_continuous.ContinuousOnAdd.At(
								a.TermAs[Fun[Real, Real]]("λx:real. m"), a.TermAs[Fun[Real, Real]]("λx:real. s * x"), line)))
					a.Show(
						"so it is Borel measurable",
						By(
							continuous,
							borel_function.ContinuousBorelMeasurable.At(affine),
							measurable_function.RealMeasurableDef.At(
								line, a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"), affine)))
				})
			// The lower ray at b is the increasing union of the windows ⟦b − s·n, b⟧, so its
			// mass is the supremum of theirs.
			leftWindowMass := ctx.Lemma(Statement{
				Binders: "∀μ:(set(real) → extended_nonneg_real). ∀b s:real.",
				Hypotheses: []string{
					"measure_on(𝕌, borel_sets(real_topology), μ)",
					"&0 < s",
				},
				Conclusion: "μ({x:real | x ≤ b}) = extended_sup(image(λn:num. μ(⟦b - s * &n, b⟧), 𝕌))",
			},
				func(
					a *Argument,
					μ *Arrow[Set[Real], extended_nonneg_real.ExtendedNonnegReal],
					b, s *Expr[Real],
					measure, sPositive Fact,
				) {
					W, windows := a.LetAs[Fun2[Nat, Real, Bool]]("W", "λn:num. ⟦b - s * &n, b⟧")
					windowsBorel := a.Have(
						"every window is Borel",
						"∀n:num. W(n) ∈ borel_sets(real_topology)",
						Derive(func(c *Argument) {
							c.FixAs[Nat]("n")
							c.Show(
								"a closed interval is Borel",
								By(Normalized, windows, borel_function.ClosedIntervalBorel.At(c.TermAs[Real]("b - s * &n"), b)))
						}))
					increasing := a.Have(
						"the windows increase",
						"∀n:num. W(n) ⊆ W(n + 1)",
						Derive(func(c *Argument) {
							n := c.FixAs[Nat]("n")
							c.Show(
								"the next window reaches further left",
								Simp(Fwd(windows), Fwd(set_basic.SubsetDef), Fwd(real_topology.ClosedIntervalMembership)),
								Derive(func(d *Argument) {
									d.FixAs[Real]("x")
									inside := d.Assume()
									d.Show(
										"b − s·(n + 1) lies below b − s·n",
										ByArith(inside, sPositive, real_construction.OfNumAdd.At(n, d.TermAs[Nat]("1"))))
								}))
						}))
					cover := a.Have(
						"a point lies at or below b exactly when some window holds it",
						"∀x:real. x ≤ b ⇔ ∃n:num. x ∈ W(n)",
						Derive(func(c *Argument) {
							x := c.FixAs[Real]("x")
							c.Iff()
							c.Forward(
								"a point below b lies in a window wide enough",
								func(d *Argument, below Fact) {
									n, wide := d.ObtainAs[Nat](
										"a window wider than b − x",
										"∃n:num. b - x < &n * s",
										By(sPositive, real_archimedean.Archimedean.At(s, d.TermAs[Real]("b - x"))))
									d.Take(n)
									d.Show(
										"x lies between the endpoints",
										ByArith(
											windows,
											below,
											wide,
											real_topology.ClosedIntervalMembership.At(x, d.TermAs[Real]("b - s * &n"), b)))
								})
							c.Backward(
								"a point of a window lies at or below b",
								func(d *Argument, inWindow Fact) {
									_, inside := d.UnpackAs[Nat](inWindow, "n")
									d.Show(
										"the right endpoint of every window is b",
										By(
											Normalized,
											windows,
											inside,
											real_topology.ClosedIntervalMembership.At(x, d.TermAs[Real]("b - s * &n"), b)))
								})
						}))
					union := a.Have(
						"so the windows exhaust the lower ray",
						"⋃image(W, 𝕌) = {x:real | x ≤ b}",
						BySets(cover))
					a.Show(
						"a measure is continuous along an increasing sequence",
						By(
							windowsBorel,
							increasing,
							windows,
							union,
							measure,
							measure_space.MeasureContinuousIncreasing.At(
								a.TermAs[Set[Real]]("𝕌"), a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"), μ, W)))
				})
			// Substituting x = m + √v·y: the √v the density of variance v divides by cancels
			// the factor in front, and the exponent is the standard one.
			affineDensity := ctx.Lemma(Statement{
				Binders: "∀m v x:real.",
				Hypotheses: []string{
					"&0 < v",
				},
				Conclusion: "real_sqrt(v) * normal_density(m, v, m + real_sqrt(v) * x) = normal_density(&0, &1, x)",
			},
				func(a *Argument, m, v, x *Expr[Real], vPositive Fact) {
					root := a.Have(
						"the standard deviation is positive and squares to the variance",
						"&0 < real_sqrt(v) ∧ real_sqrt(v) ^ 2 = v",
						ByArith(vPositive, real_sqrt.SqrtPos.At(v), real_sqrt.SqrtPowTwo.At(v)))
					square := a.Have(
						"the scaled point squares to v·x²",
						"(real_sqrt(v) * x) ^ 2 = v * x ^ 2",
						ByArith(root))
					shift := a.Have(
						"the displacement from the mean is the scaled point",
						"m + real_sqrt(v) * x - m = real_sqrt(v) * x",
						ByArith())
					exponent := a.Have(
						"so the exponent is the standard one",
						"-((m + real_sqrt(v) * x - m) ^ 2 / (&2 * v)) = -((x - &0) ^ 2 / (&2 * &1))",
						Simp(Fwd(shift)),
						ByArith(vPositive, square))
					normalizer := a.Have(
						"the normalizing root splits off the standard deviation",
						"real_sqrt(&2 * π * v) = real_sqrt(&2 * π * &1) * real_sqrt(v)",
						ByArith(real_sqrt.SqrtMul.At(a.TermAs[Real]("&2 * π"), v)))
					a.Show(
						"the standard deviation cancels",
						Simp(Fwd(NormalDensityDef), Fwd(exponent), Fwd(normalizer)),
						ByArith(root))
				})
			continuousNonnegativeDensity := ctx.Lemma(Statement{
				Binders: "∀m v:real.",
				Hypotheses: []string{
					"&0 < v",
				},
				Conclusion: "(∀x:real. &0 ≤ normal_density(m, v, x)) ∧ " +
					"(∀J:set(real). real_continuous_on(J, normal_density(m, v)))",
			},
				func(a *Argument, m, v *Expr[Real], vPositive Fact) {
					line := a.TermAs[Set[Real]]("𝕌")
					density := a.TermAs[Fun[Real, Real]]("normal_density(m, v)")
					a.Show(
						"the density is nonnegative and continuous",
						SplitConj(
							Case(
								"normal densities with positive variance are nonnegative",
								Derive(func(b *Argument) {
									x := b.FixAs[Real]("x")
									b.Show(
										"an exponential over a positive root",
										ByArith(
											vPositive,
											real_trigonometry.PiBounds,
											real_sqrt.SqrtPos.At(b.TermAs[Real]("&2 * π * v")),
											real_exp_log.ExpPositive.At(b.TermAs[Real]("-((x - m) ^ 2 / (&2 * v))")),
											NormalDensityDef.At(m, v, x)))
								}),
							),
							Case(
								"the normal density is continuous on each real set",
								Derive(func(b *Argument) {
									J := b.FixAs[Set[Real]]("J")
									form := b.Have(
										"the density is a scaled exponential of a quadratic",
										"normal_density(m, v) = "+
											"λx:real. &1 / real_sqrt(&2 * π * v) * exp(-(&1 / (&2 * v)) * ((x - m) * (x - m)))",
										Funext(),
										Simp(
											Fwd(NormalDensityDef),
											Fwd(real_pow.PowTwo),
											Fwd(real_field.RealDivDef),
											Fwd(real_construction.MulLeftId)),
										Derive(func(c *Argument) {
											c.FixAs[Real]("x")
											quadratic := c.Have(
												"normalize the quadratic exponent",
												"-((x - m) * (x - m) * real_inv(&2 * v)) = -real_inv(&2 * v) * ((x - m) * (x - m))",
												ByArith())
											c.Show(
												"substitute the exponent and commute the normalizing factor",
												Simp(Fwd(quadratic)),
												ByArith())
										}))
									b.Show(
										"a scaled exponential of a quadratic is continuous on the line, hence on J",
										By(
											form,
											real_exp_log.ExponentialQuadraticContinuous.At(
												m, b.TermAs[Real]("-(&1 / (&2 * v))"), b.TermAs[Real]("&1 / real_sqrt(&2 * π * v)")),
											set_order.SubsetUniv.At(J),
											real_continuous.ContinuousOnSubset.At(density, line, J)))
								}),
							)))
				})
			normalIntervalMass := ctx.Lemma(Statement{
				Binders: "∀m v l u:real.",
				Hypotheses: []string{
					"&0 < v",
					"l ≤ u",
				},
				Conclusion: "normal_distribution(m, v, ⟦l, u⟧) = " +
					"extended_of_real(real_integral(normal_density(m, v), l, u))",
			},
				func(a *Argument, m, v, l, u *Expr[Real], vPositive, ordered Fact) {
					embeddedCut := a.Have(
						"the embedding commutes with the cut to the window",
						"(λx:real. extended_of_real(COND(x ∈ ⟦l, u⟧, normal_density(m, v, x), &0))) = "+
							"λx:real. COND(x ∈ ⟦l, u⟧, extended_of_real(normal_density(m, v, x)), &0)",
						Funext(),
						Derive(func(b *Argument) {
							b.FixAs[Real]("x")
							b.Cases(b.TermAs[Bool]("x ∈ ⟦l, u⟧"))
							b.When(
								"inside the window both sides embed the density",
								func(c *Argument, inside Fact) {
									c.Show(
										"both cuts keep the density",
										Simp(Fwd(inside)),
										Basic())
								})
							b.Otherwise(
								"outside the window both sides vanish",
								func(c *Argument, outside Fact) {
									c.Show(
										"both cuts are zero",
										Simp(Fwd(outside)),
										Basic())
								})
						}))
					regular := a.Have(
						"the density is nonnegative and continuous on the window",
						"(∀x:real. &0 ≤ normal_density(m, v, x)) ∧ real_continuous_on(⟦l, u⟧, normal_density(m, v))",
						By(vPositive, At(continuousNonnegativeDensity, m, v)))
					a.Show(
						"the Lebesgue integral of a continuous nonnegative function over a window is its Riemann integral",
						Simp(Fwd(NormalDistributionDef), Fwd(density_measure.DensityMeasureDef)),
						By(
							embeddedCut,
							regular,
							vPositive,
							ordered,
							lebesgue_riemann.LebesgueNonnegIntegralOnInterval.At(
								a.TermAs[Fun[Real, Real]]("normal_density(m, v)"), l, u)))
				})
			affineIntervalMass := ctx.Lemma(Statement{
				Binders: "∀m v a b:real.",
				Hypotheses: []string{
					"&0 < v",
					"a ≤ b",
				},
				Conclusion: "normal_distribution(m, v, ⟦m + real_sqrt(v) * a, m + real_sqrt(v) * b⟧) = " +
					"normal_distribution(&0, &1, ⟦a, b⟧)",
			},
				func(arg *Argument, m, v, a, b *Expr[Real], vPositive, ordered Fact) {
					lower := arg.TermAs[Real]("m + real_sqrt(v) * a")
					upper := arg.TermAs[Real]("m + real_sqrt(v) * b")
					imageWindow := arg.Have(
						"the standard deviation is positive, so the image window is ordered",
						"&0 < real_sqrt(v) ∧ m + real_sqrt(v) * a ≤ m + real_sqrt(v) * b",
						ByArith(vPositive, ordered, real_sqrt.SqrtPos.At(v)))
					continuous := arg.Have(
						"the density is continuous on the image window",
						"real_continuous_on(⟦m + real_sqrt(v) * a, m + real_sqrt(v) * b⟧, normal_density(m, v))",
						By(vPositive, At(continuousNonnegativeDensity, m, v)))
					densityImage := arg.Have(
						"under x = m + √v·y the density, times √v, is the standard density",
						"(λy:real. normal_density(m, v, m + real_sqrt(v) * y) * real_sqrt(v)) = normal_density(&0, &1)",
						Funext(),
						Derive(func(c *Argument) {
							y := c.FixAs[Real]("y")
							c.Show(
								"the affine density relation at y",
								ByArith(vPositive, At(affineDensity, m, v, y)))
						}))
					substitution := arg.Have(
						"substitute x = m + √v·y in the Riemann integral",
						"real_integral(normal_density(m, v), m + real_sqrt(v) * a, m + real_sqrt(v) * b) = "+
							"real_integral(normal_density(&0, &1), a, b)",
						By(
							continuous,
							ordered,
							imageWindow,
							densityImage,
							real_order_ring.LessEqRefl,
							real_integral.RiemannIntegralAffineChange.At(
								arg.TermAs[Fun[Real, Real]]("normal_density(m, v)"),
								lower,
								upper,
								m,
								arg.TermAs[Real]("real_sqrt(v)"),
								a,
								b)))
					arg.Show(
						"both window masses are the Riemann integrals of their densities",
						By(
							substitution,
							vPositive,
							ordered,
							imageWindow,
							real_order_ring.ZeroLessThanOne,
							At(normalIntervalMass, m, v, lower, upper),
							At(normalIntervalMass, arg.TermAs[Real]("&0"), arg.TermAs[Real]("&1"), a, b)))
				})
			lowerRayMass := ctx.Lemma(Statement{
				Binders: "∀m v c:real.",
				Hypotheses: []string{
					"&0 < v",
				},
				Conclusion: "normal_distribution(m, v, {x:real | x ≤ m + real_sqrt(v) * c}) = " +
					"normal_distribution(&0, &1, {x:real | x ≤ c})",
			},
				func(a *Argument, m, v, c *Expr[Real], vPositive Fact) {
					line := a.TermAs[Set[Real]]("𝕌")
					borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
					law := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
						"normal_distribution(m, v)")
					standard := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
						"normal_distribution(&0, &1)")
					root := a.TermAs[Real]("real_sqrt(v)")
					measures := a.Have(
						"both laws are measures, and the standard deviation is positive",
						"measure_on(𝕌, borel_sets(real_topology), normal_distribution(m, v)) ∧ "+
							"measure_on(𝕌, borel_sets(real_topology), normal_distribution(&0, &1)) ∧ "+
							"&0 < real_sqrt(v)",
						By(
							vPositive,
							real_order_ring.ZeroLessThanOne,
							real_sqrt.SqrtPos.At(v),
							NormalDistributionProbability.At(m, v),
							NormalDistributionProbability.At(a.TermAs[Real]("&0"), a.TermAs[Real]("&1")),
							probability_space.ProbabilityOnDef.At(line, borel, law),
							probability_space.ProbabilityOnDef.At(line, borel, standard)))
					rayAsWindows := a.Have(
						"the lower ray at m + √v·c is the limit of the windows of width √v·n",
						"normal_distribution(m, v, {x:real | x ≤ m + real_sqrt(v) * c}) = "+
							"extended_sup(image(λn:num. "+
							"            normal_distribution(m, "+
							"                v, "+
							"                ⟦m + real_sqrt(v) * c - real_sqrt(v) * &n, m + real_sqrt(v) * c⟧), "+
							"        𝕌))",
						By(measures, At(leftWindowMass, law, a.TermAs[Real]("m + real_sqrt(v) * c"), root)))
					standardAsWindows := a.Have(
						"the lower ray at c is the limit of the windows of width n",
						"normal_distribution(&0, &1, {x:real | x ≤ c}) = "+
							"extended_sup(image(λn:num. normal_distribution(&0, &1, ⟦c - &1 * &n, c⟧), 𝕌))",
						By(
							measures,
							real_order_ring.ZeroLessThanOne,
							At(leftWindowMass, standard, c, a.TermAs[Real]("&1"))))
					sameWindows := a.Have(
						"corresponding windows have equal mass",
						"(λn:num. "+
							"    normal_distribution(m, "+
							"        v, "+
							"        ⟦m + real_sqrt(v) * c - real_sqrt(v) * &n, m + real_sqrt(v) * c⟧)) = "+
							"λn:num. normal_distribution(&0, &1, ⟦c - &1 * &n, c⟧)",
						Funext(),
						Derive(func(b *Argument) {
							n := b.FixAs[Nat]("n")
							endpoints := b.Have(
								"the affine images are the endpoints of the corresponding window",
								"c - &1 * &n ≤ c ∧ m + real_sqrt(v) * (c - &1 * &n) = m + real_sqrt(v) * c - real_sqrt(v) * &n",
								ByArith(real_order_ring.NumNonneg.At(n)))
							b.Show(
								"the window masses agree under the affine map",
								By(vPositive, endpoints, At(affineIntervalMass, m, v, b.TermAs[Real]("c - &1 * &n"), c)))
						}))
					a.Show(
						"equal window masses have equal limits",
						By(rayAsWindows, standardAsWindows, sameWindows))
				})
			preimageOfRay := ctx.Lemma(Statement{
				Binders: "∀m s c:real.",
				Hypotheses: []string{
					"&0 < s",
				},
				Conclusion: "preimage_on(𝕌, λy:real. m + s * y, {x:real | x ≤ m + s * c}) = {y:real | y ≤ c}",
			},
				func(a *Argument, m, s, c *Expr[Real], sPositive Fact) {
					a.Show(
						"a positive scaling preserves the order",
						Simp(Fwd(set_basic.Extension)),
						Derive(func(b *Argument) {
							b.FixAs[Real]("x")
							order := b.Have(
								"positive scaling preserves the lower-ray order",
								"m + s * x ≤ m + s * c ⇔ x ≤ c",
								ByArith(sPositive))
							b.Show(
								"read the lower-ray preimage pointwise",
								BySets(order))
						}))
				})
			return ctx.Theorem(headline,
				func(a *Argument, m, v *Expr[Real], h *Arrow[Real, Real], vPositive, hBorel Fact) {
					line := a.TermAs[Set[Real]]("𝕌")
					borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
					law := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
						"normal_distribution(m, v)")
					standard := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
						"normal_distribution(&0, &1)")
					affine := a.TermAs[Fun[Real, Real]]("λx:real. m + real_sqrt(v) * x")
					image := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
						"pushforward_measure(𝕌, normal_distribution(&0, &1), λx:real. m + real_sqrt(v) * x)")
					root := a.TermAs[Real]("real_sqrt(v)")
					laws := a.Have(
						"both laws are probabilities",
						"probability_on(𝕌, borel_sets(real_topology), normal_distribution(m, v)) ∧ "+
							"probability_on(𝕌, borel_sets(real_topology), normal_distribution(&0, &1))",
						By(
							vPositive,
							real_order_ring.ZeroLessThanOne,
							NormalDistributionProbability.At(m, v),
							NormalDistributionProbability.At(a.TermAs[Real]("&0"), a.TermAs[Real]("&1"))))
					affineBorel := a.Have(
						"the affine map is Borel measurable",
						"measurable_map(𝕌, "+
							"    borel_sets(real_topology), "+
							"    𝕌, "+
							"    borel_sets(real_topology), "+
							"    λx:real. m + real_sqrt(v) * x)",
						By(At(affineMapMeasurable, m, root)))
					imageLaw := a.Have(
						"so the image of the standard law under it is a probability",
						"probability_on(𝕌, "+
							"    borel_sets(real_topology), "+
							"    pushforward_measure(𝕌, normal_distribution(&0, &1), λx:real. m + real_sqrt(v) * x))",
						By(
							laws,
							affineBorel,
							borel_function.LineBorelSigmaAlgebra,
							random_variable.DistributionProbability.At(line, borel, standard, line, borel, affine)))
					lowerRays := a.Have(
						"the two laws agree on the lower rays at the affine images",
						"∀c:real. "+
							"    normal_distribution(m, v, {x:real | x ≤ m + real_sqrt(v) * c}) = "+
							"    pushforward_measure(𝕌, "+
							"        normal_distribution(&0, &1), "+
							"        λx:real. m + real_sqrt(v) * x, "+
							"        {x:real | x ≤ m + real_sqrt(v) * c})",
						Derive(func(b *Argument) {
							c := b.FixAs[Real]("c")
							b.Show(
								"the preimage of such a ray is the lower ray at c",
								By(
									vPositive,
									real_sqrt.SqrtPos.At(v),
									At(preimageOfRay, m, root, c),
									At(lowerRayMass, m, v, c),
									measure_space.PushforwardMeasureDef.At(
										line, standard, affine, b.TermAs[Set[Real]]("{x:real | x ≤ m + real_sqrt(v) * c}"))))
						}))
					everyLowerRay := a.Have(
						"so they agree on every lower ray",
						"∀b:real. "+
							"    normal_distribution(m, v, {x:real | x ≤ b}) = "+
							"    pushforward_measure(𝕌, "+
							"        normal_distribution(&0, &1), "+
							"        λx:real. m + real_sqrt(v) * x, "+
							"        {x:real | x ≤ b})",
						Derive(func(c *Argument) {
							c.FixAs[Real]("b")
							threshold := c.Have(
								"the affine map reaches b at the coordinate (b − m)/√v",
								"b = m + real_sqrt(v) * ((b - m) / real_sqrt(v))",
								ByArith(
									vPositive,
									real_sqrt.SqrtPos.At(v),
									real_order_field.EqDivMulLeft.At(
										c.TermAs[Real]("(b - m) / real_sqrt(v)"), c.TermAs[Real]("b - m"), root)))
							c.Show(
								"compare the lower rays at the matching thresholds",
								By(lowerRays.At(c.TermAs[Real]("(b - m) / real_sqrt(v)")), threshold))
						}))
					onBorel := a.Have(
						"so they agree on every Borel set",
						Statement{
							Binders: "∀E:set(real).",
							Hypotheses: []string{
								"E ∈ borel_sets(real_topology)",
							},
							Conclusion: "normal_distribution(m, v, E) = " +
								"pushforward_measure(𝕌, normal_distribution(&0, &1), λx:real. m + real_sqrt(v) * x, E)",
						},
						Derive(func(c *Argument) {
							E := c.FixAs[Set[Real]]("E")
							eBorel := c.Assume()
							c.Show(
								"a Borel probability on the line is determined by its lower rays",
								By(
									everyLowerRay,
									eBorel,
									laws,
									imageLaw,
									random_variable.ProbabilityDeterminedByLowerRays.At(law, image, E)))
						}))
					sameLaw := a.Have(
						"equal laws give h the same integrability and expectation",
						"(real_integrable(𝕌, borel_sets(real_topology), normal_distribution(m, v), h) ⇔ "+
							"    real_integrable(𝕌, "+
							"        borel_sets(real_topology), "+
							"        pushforward_measure(𝕌, normal_distribution(&0, &1), λx:real. m + real_sqrt(v) * x), "+
							"        h)) ∧ "+
							"expectation(𝕌, borel_sets(real_topology), normal_distribution(m, v), h) = "+
							"expectation(𝕌, "+
							"    borel_sets(real_topology), "+
							"    pushforward_measure(𝕌, normal_distribution(&0, &1), λx:real. m + real_sqrt(v) * x), "+
							"    h)",
						By(
							onBorel,
							borel_function.LineBorelSigmaAlgebra,
							probability_space.ExpectationDef,
							measure_integral.IntegralEqualMeasures.At(line, borel, law, image, h)))
					transfer := a.Have(
						"an expectation under an image law is the expectation of the composite",
						"(real_integrable(𝕌, "+
							"        borel_sets(real_topology), "+
							"        pushforward_measure(𝕌, normal_distribution(&0, &1), λx:real. m + real_sqrt(v) * x), "+
							"        h) ⇔ "+
							"    real_integrable(𝕌, "+
							"        borel_sets(real_topology), "+
							"        normal_distribution(&0, &1), "+
							"        λy:real. h(m + real_sqrt(v) * y))) ∧ "+
							"expectation(𝕌, "+
							"    borel_sets(real_topology), "+
							"    pushforward_measure(𝕌, normal_distribution(&0, &1), λx:real. m + real_sqrt(v) * x), "+
							"    h) = "+
							"expectation(𝕌, "+
							"    borel_sets(real_topology), "+
							"    normal_distribution(&0, &1), "+
							"    λy:real. h(m + real_sqrt(v) * y))",
						By(
							hBorel,
							laws,
							affineBorel,
							borel_function.LineBorelSigmaAlgebra,
							probability_space.ProbabilityOnDef.At(line, borel, standard),
							random_variable.ExpectationPushforward.At(line, borel, standard, line, borel, affine, h),
							functions.ComposeApply.At(h, affine)))
					a.Show(
						"chain the two identifications",
						By(sameLaw, transfer))
				})
		}),
})}
