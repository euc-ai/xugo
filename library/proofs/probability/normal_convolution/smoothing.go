package normal_convolution

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/borel_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/product_measure"
	"github.com/euc-ai/xugo/library/proofs/probability/normal_distribution"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/probability/random_variable"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// NormalDistributionConvolutionExpectation — integrate a test of the sum
// by taking successive expectations against the two normal laws.
var NormalDistributionConvolutionExpectation = normalDistributionConvolutionExpectationThm{family.Add(registry.ProofEntry{
	Name: "NormalDistributionConvolutionExpectation",
	Key:  "prop_8bb1427954257a5e",
	Build: family.Theorem(Statement{
		Binders: "∀a b s t:real. ∀h:(real → real).",
		Hypotheses: []string{
			"&0 < s",
			"&0 < t",
			"real_measurable(𝕌, borel_sets(real_topology), h)",
			"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(a + b, s + t), h)",
		},
		Conclusion: "expectation(𝕌, borel_sets(real_topology), normal_distribution(a + b, s + t), h) = " +
			"expectation(𝕌, " +
			"    borel_sets(real_topology), " +
			"    normal_distribution(a, s), " +
			"    λx:real. " +
			"        expectation(𝕌, borel_sets(real_topology), normal_distribution(b, t), λy:real. h(x + y)))",
		Abbrev: Abbrev{
			{Name: "pairSigma", Text: "product_sigma(𝕌, " +
				"    borel_sets(real_topology), " +
				"    𝕌, " +
				"    borel_sets(real_topology))"},
			{Name: "product", Text: "product_measure(𝕌, " +
				"    borel_sets(real_topology), " +
				"    normal_distribution(a, s), " +
				"    normal_distribution(b, t))"},
			{Name: "sumMap", Text: "λp:prod(real, real). fst(p) + snd(p)"},
		},
	}, func(
		arg *Argument,
		a, b, s, t *Expr[Real],
		h *Arrow[Real, Real],
		sPositive, tPositive, hBorel, hIntegrable Fact,
	) {
		line := arg.TermAs[Set[Real]]("𝕌")
		borel := arg.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
		pairs := arg.TermAs[Set[Prod[Real, Real]]]("set_cross(𝕌, 𝕌)")
		pairSigma := arg.TermAs[Set[Set[Prod[Real, Real]]]]("«pairSigma»")
		lawA := arg.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
			"normal_distribution(a, s)")
		lawB := arg.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
			"normal_distribution(b, t)")
		lawSum := arg.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
			"normal_distribution(a + b, s + t)")
		product := arg.TermAs[Fun[Set[Prod[Real, Real]], extended_nonneg_real.ExtendedNonnegReal]](
			"«product»")
		image := arg.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
			"pushforward_measure(set_cross(𝕌, 𝕌), «product», «sumMap»)")
		sumMap := arg.TermAs[Fun[Prod[Real, Real], Real]]("«sumMap»")
		first := arg.TermAs[Fun[Prod[Real, Real], Real]]("λp:prod(real, real). fst(p)")
		second := arg.TermAs[Fun[Prod[Real, Real], Real]]("λp:prod(real, real). snd(p)")
		testOfSum := arg.TermAs[Fun[Prod[Real, Real], Real]]("λp:prod(real, real). h(fst(p) + snd(p))")

		laws := arg.Have(
			"both normal laws are probability measures",
			"probability_on(𝕌, borel_sets(real_topology), normal_distribution(a, s)) ∧ "+
				"probability_on(𝕌, borel_sets(real_topology), normal_distribution(b, t))",
			By(
				sPositive,
				tPositive,
				normal_distribution.NormalDistributionProbability.At(a, s),
				normal_distribution.NormalDistributionProbability.At(b, t)))
		measures := arg.Have(
			"so both are measures on the Borel sets of the line, a σ-algebra",
			"measure_on(𝕌, borel_sets(real_topology), normal_distribution(a, s)) ∧ "+
				"measure_on(𝕌, borel_sets(real_topology), normal_distribution(b, t)) ∧ "+
				"sigma_algebra_on(𝕌, borel_sets(real_topology))",
			By(
				laws,
				probability_space.ProbabilityOnDef.At(line, borel, lawA),
				probability_space.ProbabilityOnDef.At(line, borel, lawB),
				borel_function.LineBorelSigmaAlgebra))
		sigmaFinite := arg.Have(
			"a probability measure is σ-finite",
			"sigma_finite_on(𝕌, borel_sets(real_topology), normal_distribution(a, s)) ∧ "+
				"sigma_finite_on(𝕌, borel_sets(real_topology), normal_distribution(b, t))",
			By(
				laws,
				probability_space.ProbabilitySigmaFinite.At(line, borel, lawA),
				probability_space.ProbabilitySigmaFinite.At(line, borel, lawB)))
		productMeasure := arg.Have(
			"the product of the two laws is a measure on the product σ-algebra",
			"measure_on(set_cross(𝕌, 𝕌), «pairSigma», «product»)",
			By(
				measures,
				sigmaFinite,
				product_measure.ProductMeasureOn.At(line, borel, lawA, line, borel, lawB)))
		projections := arg.Have(
			"the product σ-algebra is a σ-algebra making both projections measurable",
			"sigma_algebra_on(set_cross(𝕌, 𝕌), «pairSigma») ∧ "+
				"measurable_map(set_cross(𝕌, 𝕌), "+
				"    «pairSigma», "+
				"    𝕌, "+
				"    borel_sets(real_topology), "+
				"    λp:prod(real, real). fst(p)) ∧ "+
				"measurable_map(set_cross(𝕌, 𝕌), "+
				"    «pairSigma», "+
				"    𝕌, "+
				"    borel_sets(real_topology), "+
				"    λp:prod(real, real). snd(p))",
			By(measures, productMeasure, measurable_space.ProductSigmaProjections.At(line, borel, line, borel)))
		coordinates := arg.Have(
			"so both coordinates are measurable functions on the pairs",
			"real_measurable(set_cross(𝕌, 𝕌), «pairSigma», λp:prod(real, real). fst(p)) ∧ "+
				"real_measurable(set_cross(𝕌, 𝕌), «pairSigma», λp:prod(real, real). snd(p))",
			By(
				projections,
				measurable_function.RealMeasurableDef.At(pairs, pairSigma, first),
				measurable_function.RealMeasurableDef.At(pairs, pairSigma, second)))
		sumMeasurable := arg.Have(
			"and so is their sum",
			"measurable_map(set_cross(𝕌, 𝕌), «pairSigma», 𝕌, borel_sets(real_topology), «sumMap»)",
			By(
				projections,
				coordinates,
				measurable_function.RealMeasurableDef.At(pairs, pairSigma, sumMap),
				measurable_function.RealMeasurableAdd.At(pairs, pairSigma, first, second)))
		allPairs := arg.Have(
			"every pair of reals lies in 𝕌 × 𝕌",
			"set_cross⟨A:real, B:real⟩(𝕌, 𝕌) = 𝕌",
			BySets(
				set_product.InCrossProjections.Inst(TypeBinder.BindA[Real](), TypeBinder.BindB[Real]()),
				set_basic.InUniv.Inst[Real]()))
		lawOfSum := arg.Have(
			"the image of the product under the sum is the normal law of the sum",
			Statement{
				Binders: "∀E:set(real).",
				Hypotheses: []string{
					"E ∈ borel_sets(real_topology)",
				},
				Conclusion: "pushforward_measure(set_cross(𝕌, 𝕌), «product», «sumMap», E) = " +
					"normal_distribution(a + b, s + t, E)",
			},
			Derive(func(c *Argument) {
				E := c.FixAs[Set[Real]]("E")
				eBorel := c.Assume()
				preimage := c.Have(
					"the preimage of E under the sum is the set of pairs whose sum lies in E",
					"preimage_on(set_cross(𝕌, 𝕌), «sumMap», E) = {p:prod(real, real) | fst(p) + snd(p) ∈ E}",
					BySets(allPairs))
				c.Show(
					"the mass of that set is the convolution of the two normal laws",
					By(
						preimage,
						eBorel,
						sPositive,
						tPositive,
						measure_space.PushforwardMeasureDef.At(pairs, product, sumMap, E),
						NormalDistributionConvolution.At(a, b, s, t, E)))
			}))
		sameLaw := arg.Have(
			"the image law and the normal law of the sum give h the same integrability and expectation",
			"(real_integrable(𝕌, "+
				"        borel_sets(real_topology), "+
				"        pushforward_measure(set_cross(𝕌, 𝕌), «product», «sumMap»), "+
				"        h) ⇔ "+
				"    real_integrable(𝕌, borel_sets(real_topology), normal_distribution(a + b, s + t), h)) ∧ "+
				"expectation(𝕌, "+
				"    borel_sets(real_topology), "+
				"    pushforward_measure(set_cross(𝕌, 𝕌), «product», «sumMap»), "+
				"    h) = "+
				"expectation(𝕌, borel_sets(real_topology), normal_distribution(a + b, s + t), h)",
			By(
				lawOfSum,
				measures,
				probability_space.ExpectationDef,
				measure_integral.IntegralEqualMeasures.At(line, borel, image, lawSum, h)))
		composite := arg.Have(
			"h after the sum is h of the sum",
			"h ∘ (λp:prod(real, real). fst(p) + snd(p)) = λp:prod(real, real). h(fst(p) + snd(p))",
			Funext(),
			arg.ForEach(
				func(p *Expr[Prod[Real, Real]]) Action { return By(functions.ComposeApply.At(h, sumMap)) }))
		transfer := arg.Have(
			"the expectation under the image law is the expectation of h of the sum under the product",
			"(real_integrable(𝕌, "+
				"        borel_sets(real_topology), "+
				"        pushforward_measure(set_cross(𝕌, 𝕌), «product», «sumMap»), "+
				"        h) ⇔ "+
				"    real_integrable(set_cross(𝕌, 𝕌), "+
				"        «pairSigma», "+
				"        «product», "+
				"        λp:prod(real, real). h(fst(p) + snd(p)))) ∧ "+
				"expectation(𝕌, "+
				"    borel_sets(real_topology), "+
				"    pushforward_measure(set_cross(𝕌, 𝕌), «product», «sumMap»), "+
				"    h) = "+
				"expectation(set_cross(𝕌, 𝕌), «pairSigma», «product», λp:prod(real, real). h(fst(p) + snd(p)))",
			By(
				composite,
				hBorel,
				measures,
				productMeasure,
				sumMeasurable,
				random_variable.ExpectationPushforward.At(pairs, pairSigma, product, line, borel, sumMap, h)))
		onPairs := arg.Have(
			"h of the sum is integrable under the product, with "+
				"the expectation of h under the normal law of the sum",
			"real_integrable(set_cross(𝕌, 𝕌), "+
				"    «pairSigma», "+
				"    «product», "+
				"    λp:prod(real, real). h(fst(p) + snd(p))) ∧ "+
				"expectation(set_cross(𝕌, 𝕌), «pairSigma», «product», λp:prod(real, real). h(fst(p) + snd(p))) = "+
				"expectation(𝕌, borel_sets(real_topology), normal_distribution(a + b, s + t), h)",
			By(transfer, sameLaw, hIntegrable))
		fubini := arg.Have(
			"Fubini: the integral under the product is the iterated integral",
			"measure_integral(set_cross(𝕌, 𝕌), "+
				"    «pairSigma», "+
				"    «product», "+
				"    λp:prod(real, real). h(fst(p) + snd(p))) = "+
				"measure_integral(𝕌, "+
				"    borel_sets(real_topology), "+
				"    normal_distribution(a, s), "+
				"    λx:real. "+
				"        measure_integral(𝕌, "+
				"            borel_sets(real_topology), "+
				"            normal_distribution(b, t), "+
				"            λy:real. h(x + y)))",
			By(
				sigmaFinite,
				onPairs,
				product_measure.ProductIntegral.At(
					line, borel, lawA, line, borel, lawB, arg.TermAs[Op[Real]]("λx:real. λy:real. h(x + y)"))))
		innerExpectation := arg.Have(
			"each inner integral is an expectation under the second law",
			"(λx:real. "+
				"    measure_integral(𝕌, "+
				"        borel_sets(real_topology), "+
				"        normal_distribution(b, t), "+
				"        λy:real. h(x + y))) = "+
				"λx:real. expectation(𝕌, borel_sets(real_topology), normal_distribution(b, t), λy:real. h(x + y))",
			Funext(),
			Derive(func(c *Argument) {
				c.FixAs[Real]("x")
				c.Show(
					"an expectation is the integral",
					By(probability_space.ExpectationDef.At(
						line, borel, lawB, c.TermAs[Fun[Real, Real]]("λy:real. h(x + y)"))))
			}))
		iterated := arg.Have(
			"the expectation under the product is the iterated expectation",
			"expectation(set_cross(𝕌, 𝕌), «pairSigma», «product», λp:prod(real, real). h(fst(p) + snd(p))) = "+
				"expectation(𝕌, "+
				"    borel_sets(real_topology), "+
				"    normal_distribution(a, s), "+
				"    λx:real. "+
				"        expectation(𝕌, borel_sets(real_topology), normal_distribution(b, t), λy:real. h(x + y)))",
			By(
				Normalized,
				innerExpectation,
				fubini,
				probability_space.ExpectationDef.At(pairs, pairSigma, product, testOfSum),
				probability_space.ExpectationDef.At(
					line,
					borel,
					lawA,
					arg.TermAs[Fun[Real, Real]](
						"λx:real. "+
							"    expectation(𝕌, borel_sets(real_topology), normal_distribution(b, t), λy:real. h(x + y))"))))
		arg.Show(
			"both sides are the expectation of h of the sum under the product",
			By(iterated, onPairs))
	}),
})}

// StandardNormalSmoothingSemigroup combines two successive standard-normal
// averages into one average with the sum of the variances.
var StandardNormalSmoothingSemigroup = standardNormalSmoothingSemigroupThm{family.Add(registry.ProofEntry{
	Name: "StandardNormalSmoothingSemigroup",
	Key:  "prop_b5a6d62be886e3e",
	Build: family.Sections(Statement{
		Binders: "∀h:(real → real). ∀a u v:real.",
		Hypotheses: []string{
			"&0 ≤ u",
			"&0 ≤ v",
			"real_measurable(𝕌, borel_sets(real_topology), h)",
			"&0 < u ∧ &0 < v ⇒ " +
				"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(a, u + v), h) ∧ " +
				"real_measurable(𝕌, " +
				"    borel_sets(real_topology), " +
				"    λx:real. " +
				"        expectation(𝕌, borel_sets(real_topology), normal_distribution(&0, v), λy:real. h(x + y)))",
		},
		Conclusion: "expectation(𝕌, " +
			"    borel_sets(real_topology), " +
			"    normal_distribution(&0, &1), " +
			"    λx:real. " +
			"        expectation(𝕌, " +
			"            borel_sets(real_topology), " +
			"            normal_distribution(&0, &1), " +
			"            λy:real. h(a + real_sqrt(u) * x + real_sqrt(v) * y))) = " +
			"expectation(𝕌, " +
			"    borel_sets(real_topology), " +
			"    normal_distribution(&0, &1), " +
			"    λy:real. h(a + real_sqrt(u + v) * y))",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// A Borel function of the line stays Borel after a translation: the translation is a
			// constant plus the identity, and a Borel function of a measurable map is measurable.
			translateMeasurable := ctx.Lemma(Statement{
				Binders: "∀h:(real → real). ∀x:real.",
				Hypotheses: []string{
					"real_measurable(𝕌, borel_sets(real_topology), h)",
				},
				Conclusion: "real_measurable(𝕌, borel_sets(real_topology), λy:real. h(x + y))",
			},
				func(a *Argument, h *Arrow[Real, Real], x *Expr[Real], hBorel Fact) {
					line := a.TermAs[Set[Real]]("𝕌")
					borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
					identity := a.TermAs[Fun[Real, Real]]("λy:real. y")
					translation := a.Have(
						"the translation by x, a constant plus the identity, is Borel measurable",
						"real_measurable(𝕌, borel_sets(real_topology), λy:real. x + y)",
						By(
							borel_function.LineBorelSigmaAlgebra,
							borel_function.RealMeasurableIdentity,
							measurable_function.RealMeasurableConst.At(line, borel, x),
							measurable_function.RealMeasurableAdd.At(
								line, borel, a.TermAs[Fun[Real, Real]]("λy:real. x"), identity)))
					a.Show(
						"h after the translation is a Borel function of a measurable map",
						By(
							translation,
							hBorel,
							borel_function.RealMeasurableCompose.At(
								line, borel, a.TermAs[Fun[Real, Real]]("λy:real. x + y"), h)))
				})
			return ctx.Theorem(headline,
				func(
					arg *Argument,
					h *Arrow[Real, Real],
					a, u, v *Expr[Real],
					uNonnegative, vNonnegative, hBorel, positiveCase Fact,
				) {
					line := arg.TermAs[Set[Real]]("𝕌")
					borel := arg.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
					zero, one := arg.TermAs[Real]("&0"), arg.TermAs[Real]("&1")
					standard := arg.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
						"normal_distribution(&0, &1)")
					standardLaw := arg.Have(
						"the standard normal is a probability measure",
						"probability_on(𝕌, borel_sets(real_topology), normal_distribution(&0, &1))",
						ByArith(normal_distribution.NormalDistributionProbability.At(zero, one)))
					arg.Cases(arg.TermAs[Bool]("u = &0"))
					arg.When(
						"with no outer variance the outer integrand is constant",
						func(b *Argument, uZero Fact) {
							b.Show(
								"the outer average of a constant is that constant",
								Simp(Fwd(real_construction.AddLeftId), Fwd(uZero)),
								Simp(Rev(real_sqrt.SqrtZero), Fwd(real_ring.MulLeftZero), Fwd(real_ring.AddRightId)),
								By(
									standardLaw,
									probability_space.ExpectationConstant.At(
										line,
										borel,
										standard,
										b.TermAs[Real](
											"expectation(𝕌, "+
												"    borel_sets(real_topology), "+
												"    normal_distribution(&0, &1), "+
												"    λy:real. h(a + real_sqrt(v) * y))"))))
						})
					arg.Otherwise(
						"the outer variance is positive",
						func(b *Argument, uNonzero Fact) {
							b.Cases(b.TermAs[Bool]("v = &0"))
							b.When(
								"with no inner variance the inner integrand is constant",
								func(c *Argument, vZero Fact) {
									inner := c.Have(
										"the inner average of a constant is that constant",
										"(λx:real. "+
											"    expectation(𝕌, "+
											"        borel_sets(real_topology), "+
											"        normal_distribution(&0, &1), "+
											"        λy:real. h(a + real_sqrt(u) * x))) = "+
											"λy:real. h(a + real_sqrt(u) * y)",
										Funext(),
										Derive(func(d *Argument) {
											d.FixAs[Real]("x")
											d.Show(
												"the standard normal is a probability, so it averages a constant to itself",
												By(
													standardLaw,
													probability_space.ExpectationConstant.At(
														line, borel, standard, d.TermAs[Real]("h(a + real_sqrt(u) * x)"))))
										}))
									c.Show(
										"with √0 = 0 the double average is the single one",
										Simp(Rev(real_sqrt.SqrtZero), Fwd(real_ring.MulLeftZero), Fwd(real_ring.AddRightId), Fwd(vZero)),
										By(inner))
								})
							b.Otherwise(
								"both variances are positive: convolve the two normal laws",
								func(c *Argument, vNonzero Fact) {
									positive := c.Have(
										"both variances are positive",
										"&0 < u ∧ &0 < v",
										ByArith(uNonzero, vNonzero, uNonnegative, vNonnegative))
									combined := c.Have(
										"h is integrable for the combined law and its inner average is Borel",
										"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(a, u + v), h) ∧ "+
											"real_measurable(𝕌, "+
											"    borel_sets(real_topology), "+
											"    λx:real. "+
											"        expectation(𝕌, borel_sets(real_topology), normal_distribution(&0, v), λy:real. h(x + y)))",
										By(positive, positiveCase))
									convolution := c.Have(
										"the law of variance u + v is the convolution of those of variances u and v",
										"expectation(𝕌, borel_sets(real_topology), normal_distribution(a, u + v), h) = "+
											"expectation(𝕌, "+
											"    borel_sets(real_topology), "+
											"    normal_distribution(a, u), "+
											"    λx:real. "+
											"        expectation(𝕌, borel_sets(real_topology), normal_distribution(&0, v), λy:real. h(x + y)))",
										Derive(func(d *Argument) {
											shiftedIntegrable := d.Have(
												"h is integrable for the law of mean a + 0",
												"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(a + &0, u + v), h)",
												Simp(Fwd(real_ring.AddRightId)),
												By(combined))
											convolved := d.Have(
												"the expectation of the sum of independent normal variables of means a and 0",
												"expectation(𝕌, borel_sets(real_topology), normal_distribution(a + &0, u + v), h) = "+
													"expectation(𝕌, "+
													"    borel_sets(real_topology), "+
													"    normal_distribution(a, u), "+
													"    λx:real. "+
													"        expectation(𝕌, borel_sets(real_topology), normal_distribution(&0, v), λy:real. h(x + y)))",
												By(
													positive,
													hBorel,
													shiftedIntegrable,
													NormalDistributionConvolutionExpectation.At(a, zero, u, v, h)))
											d.Show(
												"a + 0 is a",
												convolved.Simp(Fwd(real_ring.AddRightId)),
												By(convolved))
										}))
									innerStandard := c.Have(
										"each inner average is a standard-normal average at scale √v",
										"∀x:real. "+
											"    expectation(𝕌, borel_sets(real_topology), normal_distribution(&0, v), λy:real. h(x + y)) = "+
											"    expectation(𝕌, "+
											"        borel_sets(real_topology), "+
											"        normal_distribution(&0, &1), "+
											"        λy:real. h(x + real_sqrt(v) * y))",
										Derive(func(d *Argument) {
											x := d.FixAs[Real]("x")
											translated := d.Have(
												"h after the translation by x is Borel",
												"real_measurable(𝕌, borel_sets(real_topology), λy:real. h(x + y))",
												By(hBorel, At(translateMeasurable, h, x)))
											affine := d.Have(
												"the normal law of mean 0 and variance v is the standard law scaled by √v",
												"expectation(𝕌, borel_sets(real_topology), normal_distribution(&0, v), λy:real. h(x + y)) = "+
													"expectation(𝕌, "+
													"    borel_sets(real_topology), "+
													"    normal_distribution(&0, &1), "+
													"    λy:real. h(x + (&0 + real_sqrt(v) * y)))",
												By(
													positive,
													translated,
													normal_distribution.NormalDistributionAffine.At(
														zero, v, d.TermAs[Fun[Real, Real]]("λy:real. h(x + y)"))))
											d.Show(
												"0 + √v·y is √v·y",
												affine.Simp(Fwd(real_construction.AddLeftId)),
												By(affine))
										}))
									outerStandard := c.Have(
										"the outer average is a standard-normal average at a + √u·x",
										"expectation(𝕌, "+
											"    borel_sets(real_topology), "+
											"    normal_distribution(a, u), "+
											"    λx:real. "+
											"        expectation(𝕌, "+
											"            borel_sets(real_topology), "+
											"            normal_distribution(&0, v), "+
											"            λy:real. h(x + y))) = "+
											"expectation(𝕌, "+
											"    borel_sets(real_topology), "+
											"    normal_distribution(&0, &1), "+
											"    λx:real. "+
											"        (λx:real. "+
											"            expectation(𝕌, "+
											"                borel_sets(real_topology), "+
											"                normal_distribution(&0, v), "+
											"                λy:real. h(x + y)))(a + real_sqrt(u) * x))",
										By(
											positive,
											combined,
											normal_distribution.NormalDistributionAffine.At(
												a,
												u,
												c.TermAs[Fun[Real, Real]](
													"λx:real. "+
														"    expectation(𝕌, borel_sets(real_topology), normal_distribution(&0, v), λy:real. h(x + y))"))))
									nested := c.Have(
										"the inner averages at a + √u·x are the integrand of the claim",
										"(λx:real. "+
											"    (λx:real. "+
											"        expectation(𝕌, "+
											"            borel_sets(real_topology), "+
											"            normal_distribution(&0, v), "+
											"            λy:real. h(x + y)))(a + real_sqrt(u) * x)) = "+
											"λx:real. "+
											"    expectation(𝕌, "+
											"        borel_sets(real_topology), "+
											"        normal_distribution(&0, &1), "+
											"        λy:real. h(a + real_sqrt(u) * x + real_sqrt(v) * y))",
										Funext(),
										Derive(func(d *Argument) {
											d.FixAs[Real]("x")
											d.Show(
												"the inner average at the point a + √u·x",
												By(innerStandard.At(d.TermAs[Real]("a + real_sqrt(u) * x"))))
										}))
									sum := c.Have(
										"the variances add to a positive one",
										"&0 < u + v",
										ByArith(positive))
									direct := c.Have(
										"the law of variance u + v is the standard law scaled by √(u + v)",
										"expectation(𝕌, borel_sets(real_topology), normal_distribution(a, u + v), h) = "+
											"expectation(𝕌, "+
											"    borel_sets(real_topology), "+
											"    normal_distribution(&0, &1), "+
											"    λy:real. h(a + real_sqrt(u + v) * y))",
										By(sum, hBorel, normal_distribution.NormalDistributionAffine.At(a, c.TermAs[Real]("u + v"), h)))
									c.Show(
										"both sides are the expectation under the law of variance u + v",
										outerStandard.Simp(Fwd(nested)),
										By(outerStandard, convolution, direct))
								})
						})
				})
		}),
})}
