package normal_convolution

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/measure/borel_function"
	"github.com/euc-ai/xugo/library/proofs/measure/density_measure"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/product_measure"
	"github.com/euc-ai/xugo/library/proofs/probability/normal_distribution"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_measure"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// NormalDensityConvolutionProduct — the product of the two densities factors
// into the density at the sum and a normal density in the first coordinate.
var NormalDensityConvolutionProduct = normalDensityConvolutionProductThm{family.Add(registry.ProofEntry{
	Name: "NormalDensityConvolutionProduct",
	Key:  "prop_b7c6c343fc0b082b",
	Build: family.Sections(Statement{
		Binders: "∀a b s t x z:real.",
		Hypotheses: []string{
			"&0 < s",
			"&0 < t",
		},
		Conclusion: "normal_density(a, s, x) * normal_density(b + x, t, z) = " +
			"normal_density(a + b, s + t, z) * " +
			"normal_density(a + s / (s + t) * (z - a - b), s * t / (s + t), x)",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// Completing the square: the quadratic forms in u and in d − u, of variances s and t,
			// add to one in d of variance s + t and one in u centred at s/(s + t)·d, of variance
			// s·t/(s + t). Each square is cleared of its denominator against the common
			// denominator 2·s·t·(s + t), and the cleared sides are one polynomial.
			completeSquareExponent := ctx.Lemma(Statement{
				Binders: "∀s t d u:real.",
				Hypotheses: []string{
					"&0 < s",
					"&0 < t",
				},
				Conclusion: "u * u / (&2 * s) + (d - u) * (d - u) / (&2 * t) = " +
					"d * d / (&2 * (s + t)) + (u - s / (s + t) * d) * (u - s / (s + t) * d) / (&2 * (s * t / (s + t)))",
			},
				func(a *Argument, s, t, d, u *Expr[Real], sPositive, tPositive Fact) {
					scale := a.Have(
						"the common denominator factors through the completed-square variance",
						"&2 * s * t * (s + t) = &2 * (s * t / (s + t)) * ((s + t) * (s + t))",
						ByArith(sPositive, tPositive))
					centre := a.Have(
						"the centred displacement, cleared of s + t",
						"(u - s / (s + t) * d) * (s + t) = u * (s + t) - s * d",
						ByArith(sPositive, tPositive))
					first := a.Have(
						"the first square, cleared of 2·s",
						"u * u / (&2 * s) * (&2 * s * t * (s + t)) = u * u * (t * (s + t))",
						ByArith(sPositive, tPositive))
					second := a.Have(
						"the second square, cleared of 2·t",
						"(d - u) * (d - u) / (&2 * t) * (&2 * s * t * (s + t)) = (d - u) * (d - u) * (s * (s + t))",
						ByArith(sPositive, tPositive))
					combined := a.Have(
						"the square in d, cleared of 2·(s + t)",
						"d * d / (&2 * (s + t)) * (&2 * s * t * (s + t)) = d * d * (s * t)",
						ByArith(sPositive, tPositive))
					varianceFactor := a.Have(
						"twice the completed-square variance is positive",
						"&0 < &2 * (s * t / (s + t))",
						ByArith(sPositive, tPositive))
					centred := a.Have(
						"the centred square, cleared of 2·s·t/(s + t)",
						"(u - s / (s + t) * d) * "+
							"(u - s / (s + t) * d) / "+
							"(&2 * (s * t / (s + t))) * "+
							"(&2 * s * t * (s + t)) = "+
							"(u - s / (s + t) * d) * (u - s / (s + t) * d) * ((s + t) * (s + t))",
						Simp(Fwd(scale)),
						ByArith(varianceFactor))
					regroup := a.Have(
						"regroup the centred square with (s + t)²",
						"(u - s / (s + t) * d) * (u - s / (s + t) * d) * ((s + t) * (s + t)) = "+
							"(u - s / (s + t) * d) * (s + t) * ((u - s / (s + t) * d) * (s + t))",
						ByArith())
					centredCleared := a.Have(
						"so the cleared centred square is the square of u·(s + t) − s·d",
						"(u - s / (s + t) * d) * (u - s / (s + t) * d) * ((s + t) * (s + t)) = "+
							"(u * (s + t) - s * d) * (u * (s + t) - s * d)",
						By(regroup, centre))
					cleared := a.Have(
						"multiplied by the common denominator, the two sides are one polynomial",
						"(u * u / (&2 * s) + (d - u) * (d - u) / (&2 * t)) * (&2 * s * t * (s + t)) = "+
							"(d * d / (&2 * (s + t)) + "+
							"    (u - s / (s + t) * d) * (u - s / (s + t) * d) / (&2 * (s * t / (s + t)))) * "+
							"(&2 * s * t * (s + t))",
						ByArith(combined, first, second, centred, centredCleared))
					denominator := a.Have(
						"the common denominator is positive",
						"&0 < &2 * s * t * (s + t)",
						ByArith(sPositive, tPositive))
					a.Show(
						"cancel the positive common denominator",
						ByArith(cleared, denominator))
				})
			return ctx.Theorem(headline,
				func(arg *Argument, a, b, s, t, x, z *Expr[Real], sPositive, tPositive Fact) {
					exponents := arg.Have(
						"the exponents add up as the completed square says",
						"-((x - a) ^ 2 / (&2 * s)) + -((z - (b + x)) ^ 2 / (&2 * t)) = "+
							"-((z - (a + b)) ^ 2 / (&2 * (s + t))) + "+
							"-((x - (a + s / (s + t) * (z - a - b))) ^ 2 / (&2 * (s * t / (s + t))))",
						Simp(Fwd(real_pow.PowTwo)),
						Derive(func(e *Argument) {
							displacements := e.Have(
								"write the displacements through x − a and z − a − b",
								"z - (b + x) = z - a - b - (x - a) ∧ "+
									"z - (a + b) = z - a - b ∧ "+
									"x - (a + s / (s + t) * (z - a - b)) = x - a - s / (s + t) * (z - a - b)",
								ByArith())
							square := e.Have(
								"complete the square at d = z − a − b and u = x − a",
								"(x - a) * (x - a) / (&2 * s) + (z - a - b - (x - a)) * (z - a - b - (x - a)) / (&2 * t) = "+
									"(z - a - b) * (z - a - b) / (&2 * (s + t)) + "+
									"(x - a - s / (s + t) * (z - a - b)) * "+
									"(x - a - s / (s + t) * (z - a - b)) / "+
									"(&2 * (s * t / (s + t)))",
								By(
									sPositive,
									tPositive,
									At(completeSquareExponent, s, t, e.TermAs[Real]("z - a - b"), e.TermAs[Real]("x - a"))))
							respelled := e.Have(
								"the completed square in the original displacements",
								"(x - a) * (x - a) / (&2 * s) + (z - (b + x)) * (z - (b + x)) / (&2 * t) = "+
									"(z - (a + b)) * (z - (a + b)) / (&2 * (s + t)) + "+
									"(x - (a + s / (s + t) * (z - a - b))) * "+
									"(x - (a + s / (s + t) * (z - a - b))) / "+
									"(&2 * (s * t / (s + t)))",
								By(square, displacements))
							e.Show(
								"negate both sides",
								ByArith(respelled))
						}))
					radicands := arg.Have(
						"the variances under the normalizing roots have equal products",
						"&2 * π * s * (&2 * π * t) = &2 * π * (s + t) * (&2 * π * (s * t / (s + t)))",
						ByArith(sPositive, tPositive))
					roots := arg.Have(
						"so the normalizing roots of the two sides agree",
						"real_sqrt(&2 * π * s) * real_sqrt(&2 * π * t) = "+
							"real_sqrt(&2 * π * (s + t)) * real_sqrt(&2 * π * (s * t / (s + t)))",
						By(
							radicands,
							real_sqrt.SqrtMul.At(arg.TermAs[Real]("&2 * π * s"), arg.TermAs[Real]("&2 * π * t")),
							real_sqrt.SqrtMul.At(
								arg.TermAs[Real]("&2 * π * (s + t)"), arg.TermAs[Real]("&2 * π * (s * t / (s + t))"))))
					leftSide := arg.Have(
						"the product of the two densities is one exponential over the product of the roots",
						"normal_density(a, s, x) * normal_density(b + x, t, z) = "+
							"exp(-((x - a) ^ 2 / (&2 * s)) + -((z - (b + x)) ^ 2 / (&2 * t))) / "+
							"(real_sqrt(&2 * π * s) * real_sqrt(&2 * π * t))",
						Derive(func(e *Argument) {
							densities := e.Have(
								"the two densities by definition",
								"normal_density(a, s, x) * normal_density(b + x, t, z) = "+
									"exp(-((x - a) ^ 2 / (&2 * s))) / "+
									"real_sqrt(&2 * π * s) * "+
									"(exp(-((z - (b + x)) ^ 2 / (&2 * t))) / real_sqrt(&2 * π * t))",
								By(
									normal_distribution.NormalDensityDef.At(a, s, x),
									normal_distribution.NormalDensityDef.At(e.TermAs[Real]("b + x"), t, z)))
							quotients := e.Have(
								"a product of quotients is the quotient of the products",
								"exp(-((x - a) ^ 2 / (&2 * s))) / "+
									"real_sqrt(&2 * π * s) * "+
									"(exp(-((z - (b + x)) ^ 2 / (&2 * t))) / real_sqrt(&2 * π * t)) = "+
									"exp(-((x - a) ^ 2 / (&2 * s))) * "+
									"exp(-((z - (b + x)) ^ 2 / (&2 * t))) / "+
									"(real_sqrt(&2 * π * s) * real_sqrt(&2 * π * t))",
								ByArith())
							e.Show(
								"the exponentials multiply to the exponential of the sum",
								By(
									quotients,
									densities,
									real_exp_log.ExpAdd.At(
										e.TermAs[Real]("-((x - a) ^ 2 / (&2 * s))"),
										e.TermAs[Real]("-((z - (b + x)) ^ 2 / (&2 * t))"))))
						}))
					rightSide := arg.Have(
						"the product on the right is one exponential over the product of its roots",
						"normal_density(a + b, s + t, z) * "+
							"normal_density(a + s / (s + t) * (z - a - b), s * t / (s + t), x) = "+
							"exp(-((z - (a + b)) ^ 2 / (&2 * (s + t))) + "+
							"    -((x - (a + s / (s + t) * (z - a - b))) ^ 2 / (&2 * (s * t / (s + t))))) / "+
							"(real_sqrt(&2 * π * (s + t)) * real_sqrt(&2 * π * (s * t / (s + t))))",
						Derive(func(e *Argument) {
							densities := e.Have(
								"the two densities by definition",
								"normal_density(a + b, s + t, z) * "+
									"normal_density(a + s / (s + t) * (z - a - b), s * t / (s + t), x) = "+
									"exp(-((z - (a + b)) ^ 2 / (&2 * (s + t)))) / "+
									"real_sqrt(&2 * π * (s + t)) * "+
									"(exp(-((x - (a + s / (s + t) * (z - a - b))) ^ 2 / (&2 * (s * t / (s + t))))) / "+
									"    real_sqrt(&2 * π * (s * t / (s + t))))",
								By(
									normal_distribution.NormalDensityDef.At(e.TermAs[Real]("a + b"), e.TermAs[Real]("s + t"), z),
									normal_distribution.NormalDensityDef.At(
										e.TermAs[Real]("a + s / (s + t) * (z - a - b)"),
										e.TermAs[Real]("s * t / (s + t)"),
										x)))
							quotients := e.Have(
								"a product of quotients is the quotient of the products",
								"exp(-((z - (a + b)) ^ 2 / (&2 * (s + t)))) / "+
									"real_sqrt(&2 * π * (s + t)) * "+
									"(exp(-((x - (a + s / (s + t) * (z - a - b))) ^ 2 / (&2 * (s * t / (s + t))))) / "+
									"    real_sqrt(&2 * π * (s * t / (s + t)))) = "+
									"exp(-((z - (a + b)) ^ 2 / (&2 * (s + t)))) * "+
									"exp(-((x - (a + s / (s + t) * (z - a - b))) ^ 2 / (&2 * (s * t / (s + t))))) / "+
									"(real_sqrt(&2 * π * (s + t)) * real_sqrt(&2 * π * (s * t / (s + t))))",
								ByArith())
							e.Show(
								"the exponentials multiply to the exponential of the sum",
								By(
									quotients,
									densities,
									real_exp_log.ExpAdd.At(
										e.TermAs[Real]("-((z - (a + b)) ^ 2 / (&2 * (s + t)))"),
										e.TermAs[Real]("-((x - (a + s / (s + t) * (z - a - b))) ^ 2 / (&2 * (s * t / (s + t))))"))))
						}))
					arg.Show(
						"equal exponents over equal normalizing roots",
						By(exponents, roots, leftSide, rightSide))
				})
		}),
})}

// NormalDistributionConvolution rewrites the product mass as an iterated
// density integral. After Tonelli exchanges the integrals, completing the
// square leaves a normal density of mass one in the first coordinate.
var NormalDistributionConvolution = normalDistributionConvolutionThm{family.Add(registry.ProofEntry{
	Name: "NormalDistributionConvolution",
	Key:  "prop_be6d23d7bf2de097",
	Reading: "The set of pairs is the preimage of E under addition, so the left side is " +
		"the mass the product of the two distributions gives to the event that the " +
		"coordinates sum into E: the distribution of a sum of two independent normal variables.",
	Build: family.Sections(Statement{
		Binders: "∀a b s t:real. ∀E:set(real).",
		Hypotheses: []string{
			"&0 < s",
			"&0 < t",
			"E ∈ borel_sets(real_topology)",
		},
		Conclusion: "product_measure(𝕌, " +
			"    borel_sets(real_topology), " +
			"    normal_distribution(a, s), " +
			"    normal_distribution(b, t), " +
			"    {p:prod(real, real) | fst(p) + snd(p) ∈ E}) = " +
			"normal_distribution(a + b, s + t, E)",
		Abbrev: Abbrev{
			{Name: "lebesgueSets", Text: "{E:set(real) | lebesgue_measurable(E)}"},
			{Name: "lineProbability", Text: "λμ:(set(real) → extended_nonneg_real). " +
				"    probability_on(𝕌, borel_sets(real_topology), μ)"},
			{Name: "indicator", Text: "λE:set(real). λx:real. COND(x ∈ E, real_of_num(1), real_of_num(0))"},
			{Name: "shiftEvent", Text: "λx:real. λE:set(real). {y:real | x + y ∈ E}"},
			{Name: "density", Text: "λm:real. λv:real. λz:real. extended_of_real(normal_density(m,v,z))"},
			{Name: "sectionValue", Text: "λb:real. λt:real. λE:set(real). λx:real. " +
				"    normal_distribution(b,t,«shiftEvent»(x,E))"},
			{Name: "lebesgueIntegral", Text: "λf:(real → extended_nonneg_real). " +
				"    nonneg_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, f)"},
			{Name: "sumEvent", Text: "λE:set(real). {p:prod(real,real) | fst(p) + snd(p) ∈ E}"},
			{Name: "densityCut", Text: "λm:real. λv:real. λE:set(real). λz:real. " +
				"    COND(z ∈ E, extended_of_real(normal_density(m,v,z)), extended_of_real(real_of_num(0)))"},
			{Name: "densityKernel", Text: "λa:real. " +
				"λb:real. " +
				"λs:real. " +
				"λt:real. " +
				"λE:set(real). " +
				"λx:real. " +
				"λz:real. " +
				"    extended_of_real(normal_density(a,s,x)) * «densityCut»(b+x,t,E,z)"},
			{Name: "borelProduct", Text: "product_sigma(𝕌, " +
				"    borel_sets(real_topology), " +
				"    𝕌, " +
				"    borel_sets(real_topology))"},
			{Name: "lebesgueProduct", Text: "product_sigma(𝕌, «lebesgueSets», 𝕌, «lebesgueSets»)"},
			{Name: "productMass", Text: "λa:real. λb:real. λs:real. λt:real. λE:set(real). " +
				"    product_measure(𝕌, " +
				"        borel_sets(real_topology), " +
				"        normal_distribution(a,s), " +
				"        normal_distribution(b,t), " +
				"        «sumEvent»(E))"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			borelInsideLebesgue := ctx.Lemma("borel_sets(real_topology) ⊆ «lebesgueSets»",
				func(a *Argument) {
					a.Show(
						"a Borel set is Lebesgue measurable",
						BySets(lebesgue_measure.MeasurableBorel))
				})

			translateNormalDensity := ctx.Lemma("∀m v a x:real. "+
				"    normal_density(m + a, v, x) = normal_density(m, v, x - a)",
				func(arg *Argument, m, v, a, x *Expr[Real]) {
					shift := arg.Have(
						"the displacement from the shifted mean",
						"x - (m + a) = x - a - m",
						ByArith())
					arg.Show(
						"both sides are the same exponential over the same root",
						By(
							shift,
							normal_distribution.NormalDensityDef.At(arg.TermAs[Real]("m + a"), v, x),
							normal_distribution.NormalDensityDef.At(m, v, arg.TermAs[Real]("x - a"))))
				})

			positiveDensity := ctx.Lemma(Statement{
				Binders: "∀m v x:real.",
				Hypotheses: []string{
					"&0 < v",
				},
				Conclusion: "&0 < normal_density(m, v, x)",
			},
				func(a *Argument, m, v, x *Expr[Real], vPositive Fact) {
					pi := a.Have(
						"π is positive",
						"&0 < π",
						By(real_trigonometry.PiBounds))
					radicand := a.Have(
						"so is the normalizing radicand 2πv",
						"&0 < &2 * π * v",
						ByArith(vPositive, pi))
					root := a.Have(
						"and its root",
						"&0 < real_sqrt(&2 * π * v)",
						By(radicand, real_sqrt.SqrtPos.At(a.TermAs[Real]("&2 * π * v"))))
					exponential := a.Have(
						"an exponential is positive",
						"&0 < exp(-((x - m) ^ 2 / (&2 * v)))",
						By(real_exp_log.ExpPositive.At(a.TermAs[Real]("-((x - m) ^ 2 / (&2 * v))"))))
					quotient := a.Have(
						"a quotient of positive numbers is positive",
						"&0 < exp(-((x - m) ^ 2 / (&2 * v))) / real_sqrt(&2 * π * v)",
						By(
							exponential,
							root,
							real_order_field.DivPos.At(
								a.TermAs[Real]("exp(-((x - m) ^ 2 / (&2 * v)))"), a.TermAs[Real]("real_sqrt(&2 * π * v)"))))
					a.Show(
						"the density is that quotient",
						By(quotient, normal_distribution.NormalDensityDef.At(m, v, x)))
				})

			shiftedEventBorel := ctx.Lemma(Statement{
				Binders: "∀x:real. ∀E:set(real).",
				Hypotheses: []string{
					"E ∈ borel_sets(real_topology)",
				},
				Conclusion: "«shiftEvent»(x, E) ∈ borel_sets(real_topology)",
			},
				func(a *Argument, x *Expr[Real], E *Expr[Set[Real]], eBorel Fact) {
					line := a.TermAs[Set[Real]]("𝕌")
					borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
					identity := a.TermAs[Fun[Real, Real]]("λy:real. y")
					translation := a.TermAs[Fun[Real, Real]]("λy:real. x + y")
					constant := a.Have(
						"a constant is Borel measurable",
						"real_measurable(𝕌, borel_sets(real_topology), λy:real. x)",
						By(
							borel_function.LineBorelSigmaAlgebra,
							measurable_function.RealMeasurableConst.At(line, borel, x)))
					translationBorel := a.Have(
						"so is the translation by x, the constant plus the identity",
						"real_measurable(𝕌, borel_sets(real_topology), λy:real. x + y)",
						By(
							borel_function.LineBorelSigmaAlgebra,
							borel_function.RealMeasurableIdentity,
							constant,
							measurable_function.RealMeasurableAdd.At(
								line, borel, a.TermAs[Fun[Real, Real]]("λy:real. x"), identity)))
					translationMap := a.Have(
						"the translation as a measurable map of the line",
						"measurable_map(𝕌, borel_sets(real_topology), 𝕌, borel_sets(real_topology), λy:real. x + y)",
						By(translationBorel, measurable_function.RealMeasurableDef.At(line, borel, translation)))
					preimage := a.Have(
						"the preimage of E under the translation is Borel",
						"preimage_on(𝕌, λy:real. x + y, E) ∈ borel_sets(real_topology)",
						By(
							eBorel,
							translationMap,
							measurable_space.MeasurableMapDef.At(line, borel, line, borel, translation)))
					shifted := a.Have(
						"that preimage is the shifted event",
						"preimage_on(𝕌, λy:real. x + y, E) = «shiftEvent»(x, E)",
						BySets())
					a.Show(
						"so the shifted event is Borel",
						By(preimage, shifted))
				})

			// The section of the event E at x under the law N(b, t) is the mass N(b + x, t)
			// gives E: both are standard-normal expectations of indicators, the shift
			// carried into the mean.
			shiftedNormalMass := ctx.Lemma(Statement{
				Binders: "∀b t x:real. ∀E:set(real).",
				Hypotheses: []string{
					"&0 < t",
					"E ∈ borel_sets(real_topology)",
				},
				Conclusion: "«sectionValue»(b, t, E, x) = normal_distribution(b + x, t, E)",
			},
				func(a *Argument, b, t, x *Expr[Real], E *Expr[Set[Real]], tPositive, eBorel Fact) {
					line := a.TermAs[Set[Real]]("𝕌")
					borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
					one := a.TermAs[Real]("&1")
					lawB := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
						"normal_distribution(b, t)")
					lawShifted := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
						"normal_distribution(b + x, t)")
					shiftedSet := a.TermAs[Set[Real]]("«shiftEvent»(x, E)")
					shiftedBorel := a.Have(
						"the shifted event is Borel",
						"«shiftEvent»(x, E) ∈ borel_sets(real_topology)",
						By(eBorel, At(shiftedEventBorel, x, E)))
					probabilityB := a.Have(
						"the law of mean b is a probability",
						"«lineProbability»(normal_distribution(b, t))",
						By(tPositive, normal_distribution.NormalDistributionProbability.At(b, t)))
					probabilityShifted := a.Have(
						"so is the law of mean b + x",
						"«lineProbability»(normal_distribution(b + x, t))",
						By(tPositive, normal_distribution.NormalDistributionProbability.At(a.TermAs[Real]("b + x"), t)))
					shiftedIndicator := a.Have(
						"the indicator of the shifted event is Borel",
						"real_measurable(𝕌, borel_sets(real_topology), λy:real. «indicator»(«shiftEvent»(x, E), y))",
						By(
							borel_function.LineBorelSigmaAlgebra,
							shiftedBorel,
							measurable_function.RealMeasurableIndicator.At(line, borel, shiftedSet, one)))
					indicator := a.Have(
						"the indicator of E is Borel",
						"real_measurable(𝕌, borel_sets(real_topology), λy:real. «indicator»(E, y))",
						By(
							borel_function.LineBorelSigmaAlgebra,
							eBorel,
							measurable_function.RealMeasurableIndicator.At(line, borel, E, one)))
					standardShifted := a.Have(
						"the section mass as a standard-normal expectation",
						"expectation(𝕌, "+
							"    borel_sets(real_topology), "+
							"    normal_distribution(b, t), "+
							"    λy:real. «indicator»(«shiftEvent»(x, E), y)) = "+
							"expectation(𝕌, "+
							"    borel_sets(real_topology), "+
							"    normal_distribution(&0, &1), "+
							"    λy:real. «indicator»(«shiftEvent»(x, E), b + real_sqrt(t) * y))",
						By(
							tPositive,
							shiftedIndicator,
							normal_distribution.NormalDistributionAffine.At(
								b, t, a.TermAs[Fun[Real, Real]]("λy:real. «indicator»(«shiftEvent»(x, E), y)"))))
					standardE := a.Have(
						"the mass of E under the shifted law as a standard-normal expectation",
						"expectation(𝕌, "+
							"    borel_sets(real_topology), "+
							"    normal_distribution(b + x, t), "+
							"    λy:real. «indicator»(E, y)) = "+
							"expectation(𝕌, "+
							"    borel_sets(real_topology), "+
							"    normal_distribution(&0, &1), "+
							"    λy:real. «indicator»(E, b + x + real_sqrt(t) * y))",
						By(
							tPositive,
							indicator,
							normal_distribution.NormalDistributionAffine.At(
								a.TermAs[Real]("b + x"), t, a.TermAs[Fun[Real, Real]]("λy:real. «indicator»(E, y)"))))
					sameIntegrand := a.Have(
						"the two standard-normal integrands agree: the shift moves into the mean",
						"(λy:real. «indicator»(«shiftEvent»(x, E), b + real_sqrt(t) * y)) = "+
							"λy:real. «indicator»(E, b + x + real_sqrt(t) * y)",
						Funext(),
						Derive(func(d *Argument) {
							d.FixAs[Real]("y")
							membership := d.Have(
								"membership in the shifted event, read pointwise",
								"b + real_sqrt(t) * y ∈ «shiftEvent»(x, E) ⇔ x + (b + real_sqrt(t) * y) ∈ E",
								BySets())
							regroup := d.Have(
								"regroup the shifted point",
								"x + (b + real_sqrt(t) * y) = b + x + real_sqrt(t) * y",
								ByArith())
							d.Show(
								"the two indicators test the same point",
								By(membership, regroup))
						}))
					sameExpectation := a.Have(
						"so the two indicator expectations agree",
						"expectation(𝕌, "+
							"    borel_sets(real_topology), "+
							"    normal_distribution(b, t), "+
							"    λy:real. «indicator»(«shiftEvent»(x, E), y)) = "+
							"expectation(𝕌, "+
							"    borel_sets(real_topology), "+
							"    normal_distribution(b + x, t), "+
							"    λy:real. «indicator»(E, y))",
						By(Normalized, sameIntegrand, standardShifted, standardE))
					sectionExpectation := a.Have(
						"the first expectation is the section mass, made real",
						"expectation(𝕌, "+
							"    borel_sets(real_topology), "+
							"    normal_distribution(b, t), "+
							"    λy:real. «indicator»(«shiftEvent»(x, E), y)) = "+
							"extended_to_real(«sectionValue»(b, t, E, x))",
						ByArith(
							probabilityB,
							shiftedBorel,
							probability_space.ExpectationIndicator.At(line, borel, lawB, shiftedSet, one)))
					shiftedExpectation := a.Have(
						"the second is the mass of E under the shifted law, made real",
						"expectation(𝕌, "+
							"    borel_sets(real_topology), "+
							"    normal_distribution(b + x, t), "+
							"    λy:real. «indicator»(E, y)) = "+
							"extended_to_real(normal_distribution(b + x, t, E))",
						ByArith(
							probabilityShifted,
							eBorel,
							probability_space.ExpectationIndicator.At(line, borel, lawShifted, E, one)))
					realMasses := a.Have(
						"the two masses agree as reals",
						"extended_to_real(«sectionValue»(b, t, E, x)) = extended_to_real(normal_distribution(b + x, t, E))",
						By(sameExpectation, sectionExpectation, shiftedExpectation))
					a.Show(
						"an event's mass under a probability is finite, so the two masses, agreeing as reals, agree",
						By(
							realMasses,
							probabilityB,
							shiftedBorel,
							probabilityShifted,
							eBorel,
							probability_space.ProbabilityEventFinite.At(line, borel, lawB, shiftedSet),
							probability_space.ProbabilityEventFinite.At(line, borel, lawShifted, E)))
				})

			normalDensityBorel := ctx.Lemma("∀m v:real. "+
				"    real_measurable(𝕌, borel_sets(real_topology), normal_density(m, v))",
				func(a *Argument, m, v *Expr[Real]) {
					form := a.Have(
						"the density is a constant times the exponential of a quadratic",
						"normal_density(m, v) = "+
							"λx:real. real_inv(real_sqrt(&2 * π * v)) * exp(-real_inv(&2 * v) * ((x - m) * (x - m)))",
						Funext(),
						Simp(Fwd(normal_distribution.NormalDensityDef), Fwd(real_pow.PowTwo), Fwd(real_field.RealDivDef)),
						Derive(func(b *Argument) {
							b.FixAs[Real]("x")
							exponent := b.Have(
								"regroup the inverse and the square in the exponent",
								"-((x - m) * (x - m) * real_inv(&2 * v)) = -real_inv(&2 * v) * ((x - m) * (x - m))",
								ByArith())
							b.Show(
								"the same exponential stands on both sides",
								exponent.Rw(),
								ByArith())
						}))
					continuous := a.Have(
						"an exponential of a quadratic is continuous on the line",
						"real_continuous_on(𝕌, normal_density(m, v))",
						By(
							form,
							real_exp_log.ExponentialQuadraticContinuous.At(
								m, a.TermAs[Real]("-real_inv(&2 * v)"), a.TermAs[Real]("real_inv(real_sqrt(&2 * π * v))"))))
					a.Show(
						"a function continuous on the line is Borel measurable",
						By(
							continuous,
							borel_function.ContinuousBorelMeasurable.At(a.TermAs[Fun[Real, Real]]("normal_density(m, v)"))))
				})

			densityLebesgueMeasurable := ctx.Lemma("∀m v:real. "+
				"    extended_measurable(𝕌, «lebesgueSets», λx:real. «density»(m, v, x))",
				func(a *Argument, m, v *Expr[Real]) {
					line := a.TermAs[Set[Real]]("𝕌")
					borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
					lebesgue := a.TermAs[Set[Set[Real]]]("«lebesgueSets»")
					density := a.TermAs[Fun[Real, Real]]("normal_density(m, v)")
					lebesgueMeasurable := a.Have(
						"the Borel density is Lebesgue measurable, the Borel sets being Lebesgue",
						"real_measurable(𝕌, «lebesgueSets», normal_density(m, v))",
						By(
							At(normalDensityBorel, m, v),
							borelInsideLebesgue,
							measurable_function.RealMeasurableSourceMono.At(line, borel, lebesgue, density)))
					a.Show(
						"and so is its embedding in the extended reals",
						By(
							lebesgueMeasurable,
							lebesgue_measure.LebesgueSigmaAlgebra,
							measurable_function.ExtendedMeasurableOfReal.At(line, lebesgue, density)))
				})

			normalAsDensity := ctx.Lemma("∀m v:real. "+
				"    normal_distribution(m, v) = "+
				"    density_measure(𝕌, «lebesgueSets», lebesgue_outer_measure, λx:real. «density»(m, v, x))",
				func(a *Argument, m, v *Expr[Real]) {
					a.Show(
						"the normal law is by definition the measure of its density",
						Funext(),
						a.ForEach(func(E *Expr[Set[Real]]) Action {
							return By(normal_distribution.NormalDistributionDef.At(m, v, E))
						}))
				})

			normalOnLebesgueSets := ctx.Lemma("∀m v:real. "+
				"    measure_on(𝕌, «lebesgueSets», normal_distribution(m, v))",
				func(a *Argument, m, v *Expr[Real]) {
					densityMeasure := a.Have(
						"a measurable density gives the Lebesgue sets a measure",
						"measure_on(𝕌, "+
							"    «lebesgueSets», "+
							"    density_measure(𝕌, «lebesgueSets», lebesgue_outer_measure, λx:real. «density»(m, v, x)))",
						By(
							At(densityLebesgueMeasurable, m, v),
							lebesgue_measure.LebesgueMeasureOn,
							density_measure.DensityMeasure.At(
								a.TermAs[Set[Real]]("𝕌"),
								a.TermAs[Set[Set[Real]]]("«lebesgueSets»"),
								a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("lebesgue_outer_measure"),
								a.TermAs[Fun[Real, extended_nonneg_real.ExtendedNonnegReal]](
									"λx:real. extended_of_real(normal_density(m, v, x))"))))
					a.Show(
						"the normal law is that density measure",
						By(At(normalAsDensity, m, v), densityMeasure))
				})

			normalDensityMassOne := ctx.Lemma(Statement{
				Binders: "∀m v:real.",
				Hypotheses: []string{
					"&0 < v",
				},
				Conclusion: "«lebesgueIntegral»(λz:real. «density»(m, v, z)) = extended_of_real(&1)",
			},
				func(a *Argument, m, v *Expr[Real], vPositive Fact) {
					line := a.TermAs[Set[Real]]("𝕌")
					lebesgue := a.TermAs[Set[Set[Real]]]("«lebesgueSets»")
					outer := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("lebesgue_outer_measure")
					densityFn := a.TermAs[Fun[Real, extended_nonneg_real.ExtendedNonnegReal]](
						"λx:real. extended_of_real(normal_density(m, v, x))")
					probability := a.Have(
						"the normal law is a probability",
						"«lineProbability»(normal_distribution(m, v))",
						By(vPositive, normal_distribution.NormalDistributionProbability.At(m, v)))
					total := a.Have(
						"so the line has mass one",
						"normal_distribution(m, v, 𝕌) = &1",
						By(
							probability,
							probability_space.ProbabilityOnDef.At(
								line,
								a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"),
								a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("normal_distribution(m, v)"))))
					asIntegral := a.Have(
						"the mass of the line is the integral of the density cut to the line",
						"normal_distribution(m, v, 𝕌) = «lebesgueIntegral»(λx:real. «densityCut»(m, v, 𝕌, x))",
						By(
							normal_distribution.NormalDistributionDef.At(m, v, line),
							density_measure.DensityMeasureDef.At(line, lebesgue, outer, densityFn, line)))
					uncut := a.Have(
						"cut to the whole line the density is unchanged",
						"∀x:real. x ∈ 𝕌 ⇒ «densityCut»(m, v, 𝕌, x) = «density»(m, v, x)",
						Derive(func(b *Argument) {
							b.FixAs[Real]("x")
							b.Assume()
							b.Show(
								"every point lies in the line",
								Simp(Fwd(normal_distribution.NormalDensityDef)),
								Basic())
						}))
					sameIntegral := a.Have(
						"so the two integrals agree",
						"«lebesgueIntegral»(λx:real. «densityCut»(m, v, 𝕌, x)) = "+
							"«lebesgueIntegral»(λx:real. «density»(m, v, x))",
						By(
							uncut,
							nonneg_integral.NonnegIntegralEqOn.At(
								line,
								lebesgue,
								outer,
								a.TermAs[Fun[Real, extended_nonneg_real.ExtendedNonnegReal]](
									"λx:real. COND(x ∈ 𝕌, extended_of_real(normal_density(m, v, x)), extended_of_real(&0))"),
								densityFn)))
					a.Show(
						"the normal density has unit integral",
						By(total, asIntegral, sameIntegral))
				})

			normalEventDensityIntegral := ctx.Lemma("∀m v:real. ∀E:set(real). "+
				"    normal_distribution(m, v, E) = «lebesgueIntegral»(λz:real. «densityCut»(m, v, E, z))",
				func(a *Argument, m, v *Expr[Real], E *Expr[Set[Real]]) {
					a.Show(
						"the mass of an event is the integral of the density cut to it",
						By(
							normal_distribution.NormalDistributionDef.At(m, v, E),
							density_measure.DensityMeasureDef.At(
								a.TermAs[Set[Real]]("𝕌"),
								a.TermAs[Set[Set[Real]]]("«lebesgueSets»"),
								a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("lebesgue_outer_measure"),
								a.TermAs[Fun[Real, extended_nonneg_real.ExtendedNonnegReal]](
									"λz:real. extended_of_real(normal_density(m, v, z))"),
								E)))
				})

			sumEventBorel := ctx.Lemma(Statement{
				Binders: "∀E:set(real).",
				Hypotheses: []string{
					"E ∈ borel_sets(real_topology)",
				},
				Conclusion: "«sumEvent»(E) ∈ «borelProduct»",
			},
				func(a *Argument, E *Expr[Set[Real]], eBorel Fact) {
					line := a.TermAs[Set[Real]]("𝕌")
					borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
					pairs := a.TermAs[Set[Prod[Real, Real]]]("set_cross(𝕌, 𝕌)")
					borelPairs := a.TermAs[Set[Set[Prod[Real, Real]]]]("«borelProduct»")
					first := a.TermAs[Fun[Prod[Real, Real], Real]]("λp:prod(real, real). fst(p)")
					second := a.TermAs[Fun[Prod[Real, Real], Real]]("λp:prod(real, real). snd(p)")
					sum := a.TermAs[Fun[Prod[Real, Real], Real]]("λp:prod(real, real). fst(p) + snd(p)")
					productSigma := a.Have(
						"the product of the Borel σ-algebras is a σ-algebra on the plane",
						"sigma_algebra_on(set_cross(𝕌, 𝕌), «borelProduct»)",
						By(
							borel_function.LineBorelSigmaAlgebra,
							measurable_space.ProductSigmaProjections.At(line, borel, line, borel)))
					firstMap := a.Have(
						"the first projection is measurable",
						"measurable_map(set_cross(𝕌, 𝕌), "+
							"    «borelProduct», "+
							"    𝕌, "+
							"    borel_sets(real_topology), "+
							"    λp:prod(real, real). fst(p))",
						By(
							borel_function.LineBorelSigmaAlgebra,
							measurable_space.ProductSigmaProjections.At(line, borel, line, borel)))
					secondMap := a.Have(
						"and so is the second",
						"measurable_map(set_cross(𝕌, 𝕌), "+
							"    «borelProduct», "+
							"    𝕌, "+
							"    borel_sets(real_topology), "+
							"    λp:prod(real, real). snd(p))",
						By(
							borel_function.LineBorelSigmaAlgebra,
							measurable_space.ProductSigmaProjections.At(line, borel, line, borel)))
					firstBorel := a.Have(
						"so the first coordinate is a measurable function",
						"real_measurable(set_cross(𝕌, 𝕌), «borelProduct», λp:prod(real, real). fst(p))",
						By(firstMap, measurable_function.RealMeasurableDef.At(pairs, borelPairs, first)))
					secondBorel := a.Have(
						"and so is the second",
						"real_measurable(set_cross(𝕌, 𝕌), «borelProduct», λp:prod(real, real). snd(p))",
						By(secondMap, measurable_function.RealMeasurableDef.At(pairs, borelPairs, second)))
					sumBorel := a.Have(
						"and so is their sum",
						"real_measurable(set_cross(𝕌, 𝕌), «borelProduct», λp:prod(real, real). fst(p) + snd(p))",
						By(
							productSigma,
							firstBorel,
							secondBorel,
							measurable_function.RealMeasurableAdd.At(pairs, borelPairs, first, second)))
					sumMap := a.Have(
						"the sum as a measurable map to the line",
						"measurable_map(set_cross(𝕌, 𝕌), "+
							"    «borelProduct», "+
							"    𝕌, "+
							"    borel_sets(real_topology), "+
							"    λp:prod(real, real). fst(p) + snd(p))",
						By(sumBorel, measurable_function.RealMeasurableDef.At(pairs, borelPairs, sum)))
					preimage := a.Have(
						"the preimage of E under the sum is measurable",
						"preimage_on(set_cross(𝕌, 𝕌), λp:prod(real, real). fst(p) + snd(p), E) ∈ «borelProduct»",
						By(sumMap, eBorel, measurable_space.MeasurableMapDef.At(pairs, borelPairs, line, borel, sum)))
					sumEvent := a.Have(
						"that preimage is the sum event",
						"preimage_on(set_cross(𝕌, 𝕌), λp:prod(real, real). fst(p) + snd(p), E) = «sumEvent»(E)",
						BySets(At(
							set_product.InCrossProjections.Inst(TypeBinder.BindA[Real](), TypeBinder.BindB[Real]()),
							line,
							line)))
					a.Show(
						"so the sum event is in the product σ-algebra",
						By(sumEvent, preimage))
				})

			extendedMeasurableOnLebesgue := ctx.Lemma(Statement{
				Binders: "∀f:(real → extended_nonneg_real).",
				Hypotheses: []string{
					"extended_measurable(𝕌, borel_sets(real_topology), f)",
				},
				Conclusion: "extended_measurable(𝕌, «lebesgueSets», f)",
			},
				func(a *Argument, f *Arrow[Real, extended_nonneg_real.ExtendedNonnegReal], fBorel Fact) {
					line := a.TermAs[Set[Real]]("𝕌")
					borelRays := a.Have(
						"the upper level sets of f are Borel",
						"∀r:real. {x:real | x ∈ 𝕌 ∧ extended_of_real(r) < f(x)} ∈ borel_sets(real_topology)",
						By(
							fBorel,
							borel_function.LineBorelSigmaAlgebra,
							measurable_function.ExtendedMeasurableIffRay.At(
								line, a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"), f)))
					lebesgueRays := a.Have(
						"so they are Lebesgue measurable",
						"∀r:real. {x:real | x ∈ 𝕌 ∧ extended_of_real(r) < f(x)} ∈ «lebesgueSets»",
						a.ForEach(func(r *Expr[Real]) Action { return BySets(borelRays.At(r), borelInsideLebesgue) }))
					a.Show(
						"a function with Lebesgue level sets is Lebesgue measurable",
						By(
							lebesgueRays,
							lebesgue_measure.LebesgueSigmaAlgebra,
							measurable_function.ExtendedMeasurableIffRay.At(
								line, a.TermAs[Set[Set[Real]]]("«lebesgueSets»"), f)))
				})

			integrateNormalByDensity := ctx.Lemma(Statement{
				Binders: "∀m v:real. ∀f:(real → extended_nonneg_real).",
				Hypotheses: []string{
					"extended_measurable(𝕌, «lebesgueSets», f)",
				},
				Conclusion: "nonneg_integral(𝕌, «lebesgueSets», normal_distribution(m, v), f) = " +
					"«lebesgueIntegral»(λx:real. «density»(m, v, x) * f(x))",
			},
				func(
					a *Argument,
					m, v *Expr[Real],
					f *Arrow[Real, extended_nonneg_real.ExtendedNonnegReal],
					fMeasurable Fact,
				) {
					changeOfMeasure := a.Have(
						"integrating against a density measure integrates the density times the integrand",
						"nonneg_integral(𝕌, "+
							"    «lebesgueSets», "+
							"    density_measure(𝕌, «lebesgueSets», lebesgue_outer_measure, λx:real. «density»(m, v, x)), "+
							"    f) = "+
							"«lebesgueIntegral»(λx:real. «density»(m, v, x) * f(x))",
						By(
							At(densityLebesgueMeasurable, m, v),
							fMeasurable,
							lebesgue_measure.LebesgueMeasureOn,
							density_measure.DensityMeasureNonnegIntegral.At(
								a.TermAs[Set[Real]]("𝕌"),
								a.TermAs[Set[Set[Real]]]("«lebesgueSets»"),
								a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("lebesgue_outer_measure"),
								a.TermAs[Fun[Real, extended_nonneg_real.ExtendedNonnegReal]](
									"λx:real. extended_of_real(normal_density(m, v, x))"),
								f)))
					a.Show(
						"the normal law is that density measure",
						By(At(normalAsDensity, m, v), changeOfMeasure))
				})

			sumEventSection := ctx.Lemma("∀E:set(real). ∀x:real. "+
				"    {y:real | (x, y) ∈ «sumEvent»(E)} = «shiftEvent»(x, E)",
				func(a *Argument, E *Expr[Set[Real]], x *Expr[Real]) {
					a.Show(
						"the section of the sum event at x is the event shifted by x",
						BySets(
							pairs.Fst.Inst(TypeBinder.BindA[Real](), TypeBinder.BindB[Real]()),
							pairs.Snd.Inst(TypeBinder.BindA[Real](), TypeBinder.BindB[Real]())))
				})
			sectionMasses := ctx.Lemma("∀b t:real. ∀E:set(real). "+
				"    (λx:real. normal_distribution(b, t, {y:real | (x, y) ∈ «sumEvent»(E)})) = "+
				"    λx:real. «sectionValue»(b, t, E, x)",
				func(a *Argument, b, t *Expr[Real], E *Expr[Set[Real]]) {
					a.Show(
						"each section of the sum event is a shifted event",
						Funext(),
						a.ForEach(func(x *Expr[Real]) Action { return By(At(sumEventSection, E, x)) }))
				})

			sectionMassBorel := ctx.Lemma(Statement{
				Binders: "∀b t:real. ∀E:set(real).",
				Hypotheses: []string{
					"&0 < t",
					"E ∈ borel_sets(real_topology)",
				},
				Conclusion: "extended_measurable(𝕌, " +
					"    borel_sets(real_topology), " +
					"    λx:real. «sectionValue»(b, t, E, x))",
			},
				func(a *Argument, b, t *Expr[Real], E *Expr[Set[Real]], tPositive, eBorel Fact) {
					line := a.TermAs[Set[Real]]("𝕌")
					borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
					lawB := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
						"normal_distribution(b, t)")
					probability := a.Have(
						"the law of mean b is a probability",
						"«lineProbability»(normal_distribution(b, t))",
						By(tPositive, normal_distribution.NormalDistributionProbability.At(b, t)))
					sigmaFinite := a.Have(
						"so it is σ-finite",
						"sigma_finite_on(𝕌, borel_sets(real_topology), normal_distribution(b, t))",
						By(probability, probability_space.ProbabilitySigmaFinite.At(line, borel, lawB)))
					sumEvent := a.Have(
						"the sum event is in the product σ-algebra",
						"«sumEvent»(E) ∈ «borelProduct»",
						By(eBorel, At(sumEventBorel, E)))
					sections := a.Have(
						"the section masses of a product-measurable set are measurable",
						"extended_measurable(𝕌, "+
							"    borel_sets(real_topology), "+
							"    λx:real. normal_distribution(b, t, {y:real | (x, y) ∈ «sumEvent»(E)}))",
						By(
							borel_function.LineBorelSigmaAlgebra,
							sigmaFinite,
							sumEvent,
							product_measure.ProductSectionMassMeasurable.At(
								line, borel, line, borel, lawB, a.TermAs[Set[Prod[Real, Real]]]("«sumEvent»(E)"))))
					a.Show(
						"those sections are the shifted events",
						By(sections, At(sectionMasses, b, t, E)))
				})

			productMassByDensity := ctx.Lemma(Statement{
				Binders: "∀a b s t:real. ∀E:set(real).",
				Hypotheses: []string{
					"&0 < s",
					"&0 < t",
					"E ∈ borel_sets(real_topology)",
				},
				Conclusion: "«productMass»(a, b, s, t, E) = " +
					"«lebesgueIntegral»(λx:real. «density»(a, s, x) * «sectionValue»(b, t, E, x))",
			},
				func(arg *Argument, a, b, s, t *Expr[Real], E *Expr[Set[Real]], sPositive, tPositive, eBorel Fact) {
					line := arg.TermAs[Set[Real]]("𝕌")
					borel := arg.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
					lebesgue := arg.TermAs[Set[Set[Real]]]("«lebesgueSets»")
					lawA := arg.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
						"normal_distribution(a, s)")
					lawB := arg.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
						"normal_distribution(b, t)")
					sections := arg.TermAs[Fun[Real, extended_nonneg_real.ExtendedNonnegReal]](
						"λx:real. normal_distribution(b, t, {y:real | x + y ∈ E})")
					iterated := arg.Have(
						"the product mass is the integral of the section masses",
						"«productMass»(a, b, s, t, E) = "+
							"nonneg_integral(𝕌, "+
							"    borel_sets(real_topology), "+
							"    normal_distribution(a, s), "+
							"    λx:real. «sectionValue»(b, t, E, x))",
						By(
							At(sectionMasses, b, t, E),
							product_measure.ProductMeasureDef.At(
								line, borel, lawA, lawB, arg.TermAs[Set[Prod[Real, Real]]]("«sumEvent»(E)"))))
					sectionsBorel := arg.Have(
						"the section masses are Borel",
						"extended_measurable(𝕌, borel_sets(real_topology), λx:real. «sectionValue»(b, t, E, x))",
						By(tPositive, eBorel, At(sectionMassBorel, b, t, E)))
					onLebesgue := arg.Have(
						"integrating the Borel section masses over the Lebesgue sets changes nothing",
						"nonneg_integral(𝕌, "+
							"    borel_sets(real_topology), "+
							"    normal_distribution(a, s), "+
							"    λx:real. «sectionValue»(b, t, E, x)) = "+
							"nonneg_integral(𝕌, "+
							"    «lebesgueSets», "+
							"    normal_distribution(a, s), "+
							"    λx:real. «sectionValue»(b, t, E, x))",
						By(
							sectionsBorel,
							At(normalOnLebesgueSets, a, s),
							borel_function.LineBorelSigmaAlgebra,
							borelInsideLebesgue,
							nonneg_integral.SubSigmaIntegral.At(line, lebesgue, lawA, borel, sections)))
					sectionsLebesgue := arg.Have(
						"the section masses are Lebesgue measurable",
						"extended_measurable(𝕌, «lebesgueSets», λx:real. «sectionValue»(b, t, E, x))",
						By(sectionsBorel, At(extendedMeasurableOnLebesgue, sections)))
					byDensity := arg.Have(
						"integrate them against the density of the first law",
						"nonneg_integral(𝕌, "+
							"    «lebesgueSets», "+
							"    normal_distribution(a, s), "+
							"    λx:real. «sectionValue»(b, t, E, x)) = "+
							"«lebesgueIntegral»(λx:real. «density»(a, s, x) * «sectionValue»(b, t, E, x))",
						By(sectionsLebesgue, At(integrateNormalByDensity, a, s, sections)))
					arg.Show(
						"the product mass is the density integral of the section masses",
						By(iterated, onLebesgue, byDensity))
				})

			integrateXThenZ := ctx.Lemma(Statement{
				Binders: "∀a b s t:real. ∀E:set(real).",
				Hypotheses: []string{
					"&0 < s",
					"&0 < t",
					"E ∈ borel_sets(real_topology)",
				},
				Conclusion: "«productMass»(a, b, s, t, E) = " +
					"«lebesgueIntegral»(λx:real. «lebesgueIntegral»(λz:real. «densityKernel»(a, b, s, t, E, x, z)))",
			},
				func(arg *Argument, a, b, s, t *Expr[Real], E *Expr[Set[Real]], sPositive, tPositive, eBorel Fact) {
					line := arg.TermAs[Set[Real]]("𝕌")
					lebesgue := arg.TermAs[Set[Set[Real]]]("«lebesgueSets»")
					outer := arg.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
						"lebesgue_outer_measure")
					integrands := arg.Have(
						"at each x the density times the section mass is the inner integral of the kernel",
						Statement{
							Binders: "∀x:real.",
							Hypotheses: []string{
								"x ∈ 𝕌",
							},
							Conclusion: "«density»(a, s, x) * «sectionValue»(b, t, E, x) = " +
								"«lebesgueIntegral»(λz:real. «densityKernel»(a, b, s, t, E, x, z))",
						},
						Derive(func(d *Argument) {
							x := d.FixAs[Real]("x")
							d.Assume()
							sectionIntegral := d.Have(
								"the section mass is the integral of the shifted density cut to E",
								"«sectionValue»(b, t, E, x) = «lebesgueIntegral»(λz:real. «densityCut»(b + x, t, E, z))",
								By(
									tPositive,
									eBorel,
									At(shiftedNormalMass, b, t, x, E),
									At(normalEventDensityIntegral, d.TermAs[Real]("b + x"), t, E)))
							nonnegative := d.Have(
								"the first density is nonnegative",
								"&0 ≤ normal_density(a, s, x)",
								ByArith(sPositive, At(positiveDensity, a, s, x)))
							scaled := d.Have(
								"a nonnegative constant comes out of the inner integral",
								"«lebesgueIntegral»(λz:real. «densityKernel»(a, b, s, t, E, x, z)) = "+
									"«density»(a, s, x) * «lebesgueIntegral»(λz:real. «densityCut»(b + x, t, E, z))",
								By(
									nonnegative,
									lebesgue_measure.LebesgueMeasureOn,
									nonneg_integral.NonnegIntegralScale.At(
										line,
										lebesgue,
										outer,
										d.TermAs[Fun[Real, extended_nonneg_real.ExtendedNonnegReal]](
											"λz:real. COND(z ∈ E, extended_of_real(normal_density(b + x, t, z)), extended_of_real(&0))"),
										d.TermAs[Real]("normal_density(a, s, x)"))))
							d.Show(
								"the density times the section mass is the inner integral",
								By(sectionIntegral, scaled))
						}))
					outerIntegral := arg.Have(
						"so the outer integrals agree",
						"«lebesgueIntegral»(λx:real. «density»(a, s, x) * «sectionValue»(b, t, E, x)) = "+
							"«lebesgueIntegral»(λx:real. «lebesgueIntegral»(λz:real. «densityKernel»(a, b, s, t, E, x, z)))",
						By(
							integrands,
							nonneg_integral.NonnegIntegralEqOn.At(
								line,
								lebesgue,
								outer,
								arg.TermAs[Fun[Real, extended_nonneg_real.ExtendedNonnegReal]](
									"λx:real. "+
										"    extended_of_real(normal_density(a, s, x)) * normal_distribution(b, t, {y:real | x + y ∈ E})"),
								arg.TermAs[Fun[Real, extended_nonneg_real.ExtendedNonnegReal]](
									"λx:real. "+
										"    nonneg_integral(𝕌, "+
										"        {E:set(real) | lebesgue_measurable(E)}, "+
										"        lebesgue_outer_measure, "+
										"        λz:real. "+
										"            extended_of_real(normal_density(a, s, x)) * "+
										"            COND(z ∈ E, extended_of_real(normal_density(b + x, t, z)), extended_of_real(&0)))"))))
					arg.Show(
						"the product mass as an iterated integral of the kernel",
						By(sPositive, tPositive, eBorel, outerIntegral, At(productMassByDensity, a, b, s, t, E)))
				})

			embedCutProduct := ctx.Lemma(Statement{
				Binders: "∀r q:real. ∀P:bool.",
				Hypotheses: []string{
					"&0 ≤ r",
				},
				Conclusion: "extended_of_real(r) * COND(P, extended_of_real(q), &0) = " +
					"extended_of_real(COND(P, r * q, &0))",
			},
				func(a *Argument, r, q *Expr[Real], P *Expr[Bool], rNonnegative Fact) {
					a.Show(
						"on P the embedding is multiplicative, off P both sides vanish",
						BySets(
							rNonnegative,
							extended_nonneg_real.OfRealMul.At(r, q),
							extended_nonneg_real.MulZero.At(
								a.TermAs[extended_nonneg_real.ExtendedNonnegReal]("extended_of_real(r)"))))
				})

			lebesgueTargetBorel := ctx.Lemma(Statement{
				Binders: "∀f:(prod(real, real) → real).",
				Hypotheses: []string{
					"measurable_map(set_cross(𝕌, 𝕌), «lebesgueProduct», 𝕌, «lebesgueSets», f)",
				},
				Conclusion: "real_measurable(set_cross(𝕌, 𝕌), «lebesgueProduct», f)",
			},
				func(a *Argument, f *Arrow[Prod[Real, Real], Real], lebesgueTarget Fact) {
					line := a.TermAs[Set[Real]]("𝕌")
					pairs := a.TermAs[Set[Prod[Real, Real]]]("set_cross(𝕌, 𝕌)")
					lebesguePairs := a.TermAs[Set[Set[Prod[Real, Real]]]]("«lebesgueProduct»")
					borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
					lebesgue := a.TermAs[Set[Set[Real]]]("«lebesgueSets»")
					a.Show(
						"a map measurable into the Lebesgue sets is measurable into the smaller Borel σ-algebra",
						By(
							lebesgueTarget,
							borelInsideLebesgue,
							set_basic.SubsetDef.At(borel, lebesgue),
							measurable_space.MeasurableMapDef.At(pairs, lebesguePairs, line, lebesgue, f),
							measurable_space.MeasurableMapDef.At(pairs, lebesguePairs, line, borel, f),
							measurable_function.RealMeasurableDef.At(pairs, lebesguePairs, f)))
				})

			jointKernelMeasurable := ctx.Lemma(Statement{
				Binders: "∀a b s t:real. ∀E:set(real).",
				Hypotheses: []string{
					"&0 < s",
					"&0 < t",
					"E ∈ borel_sets(real_topology)",
				},
				Conclusion: "extended_measurable(set_cross(𝕌, 𝕌), " +
					"    «lebesgueProduct», " +
					"    λp:prod(real, real). «densityKernel»(a, b, s, t, E, fst(p), snd(p)))",
			},
				func(arg *Argument, a, b, s, t *Expr[Real], E *Expr[Set[Real]], sPositive, tPositive, eBorel Fact) {
					line := arg.TermAs[Set[Real]]("𝕌")
					borel := arg.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
					lebesgue := arg.TermAs[Set[Set[Real]]]("«lebesgueSets»")
					pairs := arg.TermAs[Set[Prod[Real, Real]]]("set_cross(𝕌, 𝕌)")
					lebesguePairs := arg.TermAs[Set[Set[Prod[Real, Real]]]]("«lebesgueProduct»")
					first := arg.TermAs[Fun[Prod[Real, Real], Real]]("λp:prod(real, real). fst(p)")
					second := arg.TermAs[Fun[Prod[Real, Real], Real]]("λp:prod(real, real). snd(p)")
					minusFirst := arg.TermAs[Fun[Prod[Real, Real], Real]]("λp:prod(real, real). -fst(p)")
					difference := arg.TermAs[Fun[Prod[Real, Real], Real]]("λp:prod(real, real). snd(p) + -fst(p)")
					densityA := arg.TermAs[Fun[Real, Real]]("normal_density(a, s)")
					densityB := arg.TermAs[Fun[Real, Real]]("normal_density(b, t)")
					firstFactor := arg.TermAs[Fun[Prod[Real, Real], Real]](
						"λp:prod(real, real). normal_density(a, s, fst(p))")
					secondFactor := arg.TermAs[Fun[Prod[Real, Real], Real]](
						"λp:prod(real, real). normal_density(b + fst(p), t, snd(p))")
					product := arg.TermAs[Fun[Prod[Real, Real], Real]](
						"λp:prod(real, real). normal_density(a, s, fst(p)) * normal_density(b + fst(p), t, snd(p))")
					cutEvent := arg.TermAs[Set[Prod[Real, Real]]]("{p:prod(real, real) | snd(p) ∈ E}")
					productSigma := arg.Have(
						"the product of the Lebesgue σ-algebras is a σ-algebra on the plane",
						"sigma_algebra_on(set_cross(𝕌, 𝕌), «lebesgueProduct»)",
						By(
							lebesgue_measure.LebesgueSigmaAlgebra,
							measurable_space.ProductSigmaProjections.At(line, lebesgue, line, lebesgue)))
					firstMap := arg.Have(
						"the first projection is measurable into the Lebesgue sets",
						"measurable_map(set_cross(𝕌, 𝕌), "+
							"    «lebesgueProduct», "+
							"    𝕌, "+
							"    «lebesgueSets», "+
							"    λp:prod(real, real). fst(p))",
						By(
							lebesgue_measure.LebesgueSigmaAlgebra,
							measurable_space.ProductSigmaProjections.At(line, lebesgue, line, lebesgue)))
					secondMap := arg.Have(
						"and so is the second",
						"measurable_map(set_cross(𝕌, 𝕌), "+
							"    «lebesgueProduct», "+
							"    𝕌, "+
							"    «lebesgueSets», "+
							"    λp:prod(real, real). snd(p))",
						By(
							lebesgue_measure.LebesgueSigmaAlgebra,
							measurable_space.ProductSigmaProjections.At(line, lebesgue, line, lebesgue)))
					firstReal := arg.Have(
						"so the first coordinate is a measurable function",
						"real_measurable(set_cross(𝕌, 𝕌), «lebesgueProduct», λp:prod(real, real). fst(p))",
						By(firstMap, At(lebesgueTargetBorel, first)))
					secondReal := arg.Have(
						"and so is the second",
						"real_measurable(set_cross(𝕌, 𝕌), «lebesgueProduct», λp:prod(real, real). snd(p))",
						By(secondMap, At(lebesgueTargetBorel, second)))
					minusFirstReal := arg.Have(
						"and the negated first coordinate",
						"real_measurable(set_cross(𝕌, 𝕌), «lebesgueProduct», λp:prod(real, real). -fst(p))",
						By(firstReal, productSigma, measurable_function.RealMeasurableNeg.At(pairs, lebesguePairs, first)))
					differenceReal := arg.Have(
						"and the difference of the coordinates",
						"real_measurable(set_cross(𝕌, 𝕌), «lebesgueProduct», λp:prod(real, real). snd(p) + -fst(p))",
						By(
							secondReal,
							minusFirstReal,
							productSigma,
							measurable_function.RealMeasurableAdd.At(pairs, lebesguePairs, second, minusFirst)))
					firstBorelMap := arg.Have(
						"the first coordinate as a map to the Borel line",
						"measurable_map(set_cross(𝕌, 𝕌), "+
							"    «lebesgueProduct», "+
							"    𝕌, "+
							"    borel_sets(real_topology), "+
							"    λp:prod(real, real). fst(p))",
						By(firstReal, measurable_function.RealMeasurableDef.At(pairs, lebesguePairs, first)))
					secondBorelMap := arg.Have(
						"the second coordinate as a map to the Borel line",
						"measurable_map(set_cross(𝕌, 𝕌), "+
							"    «lebesgueProduct», "+
							"    𝕌, "+
							"    borel_sets(real_topology), "+
							"    λp:prod(real, real). snd(p))",
						By(secondReal, measurable_function.RealMeasurableDef.At(pairs, lebesguePairs, second)))
					differenceBorelMap := arg.Have(
						"the difference as a map to the Borel line",
						"measurable_map(set_cross(𝕌, 𝕌), "+
							"    «lebesgueProduct», "+
							"    𝕌, "+
							"    borel_sets(real_topology), "+
							"    λp:prod(real, real). snd(p) + -fst(p))",
						By(differenceReal, measurable_function.RealMeasurableDef.At(pairs, lebesguePairs, difference)))
					densityAMap := arg.Have(
						"the first density is a Borel map of the line",
						"measurable_map(𝕌, borel_sets(real_topology), 𝕌, borel_sets(real_topology), normal_density(a, s))",
						By(At(normalDensityBorel, a, s), measurable_function.RealMeasurableDef.At(line, borel, densityA)))
					densityBMap := arg.Have(
						"and so is the second",
						"measurable_map(𝕌, borel_sets(real_topology), 𝕌, borel_sets(real_topology), normal_density(b, t))",
						By(At(normalDensityBorel, b, t), measurable_function.RealMeasurableDef.At(line, borel, densityB)))
					firstComposite := arg.Have(
						"the first density of the first coordinate is measurable",
						"measurable_map(set_cross(𝕌, 𝕌), "+
							"    «lebesgueProduct», "+
							"    𝕌, "+
							"    borel_sets(real_topology), "+
							"    normal_density(a, s) ∘ λp:prod(real, real). fst(p))",
						By(
							firstBorelMap,
							densityAMap,
							measurable_space.MeasurableCompose.At(
								pairs, lebesguePairs, line, borel, line, borel, first, densityA)))
					secondComposite := arg.Have(
						"the second density of the difference is measurable",
						"measurable_map(set_cross(𝕌, 𝕌), "+
							"    «lebesgueProduct», "+
							"    𝕌, "+
							"    borel_sets(real_topology), "+
							"    normal_density(b, t) ∘ λp:prod(real, real). snd(p) + -fst(p))",
						By(
							differenceBorelMap,
							densityBMap,
							measurable_space.MeasurableCompose.At(
								pairs, lebesguePairs, line, borel, line, borel, difference, densityB)))
					firstFactorReal := arg.Have(
						"so the first factor of the kernel is a measurable function",
						"real_measurable(set_cross(𝕌, 𝕌), "+
							"    «lebesgueProduct», "+
							"    λp:prod(real, real). normal_density(a, s, fst(p)))",
						By(
							firstComposite,
							measurable_function.RealMeasurableDef.At(pairs, lebesguePairs, firstFactor),
							functions.ComposeApply.At(densityA, first)))
					differenceFactorReal := arg.Have(
						"and so is the second density at the difference",
						"real_measurable(set_cross(𝕌, 𝕌), "+
							"    «lebesgueProduct», "+
							"    λp:prod(real, real). normal_density(b, t, snd(p) + -fst(p)))",
						By(
							secondComposite,
							measurable_function.RealMeasurableDef.At(
								pairs,
								lebesguePairs,
								arg.TermAs[Fun[Prod[Real, Real], Real]](
									"λp:prod(real, real). normal_density(b, t, snd(p) + -fst(p))")),
							functions.ComposeApply.At(densityB, difference)))
					translated := arg.Have(
						"the second density at the difference is the shifted density at the second coordinate",
						"(λp:prod(real, real). normal_density(b, t, snd(p) + -fst(p))) = "+
							"λp:prod(real, real). normal_density(b + fst(p), t, snd(p))",
						Funext(),
						Derive(func(d *Argument) {
							d.FixAs[Prod[Real, Real]]("p")
							subtraction := d.Have(
								"the difference written as a subtraction",
								"snd(p) + -fst(p) = snd(p) - fst(p)",
								ByArith())
							d.Show(
								"translate the density by the first coordinate",
								By(
									subtraction,
									At(translateNormalDensity, b, t, d.TermAs[Real]("fst(p)"), d.TermAs[Real]("snd(p)"))))
						}))
					secondFactorReal := arg.Have(
						"so the second factor of the kernel is a measurable function",
						"real_measurable(set_cross(𝕌, 𝕌), "+
							"    «lebesgueProduct», "+
							"    λp:prod(real, real). normal_density(b + fst(p), t, snd(p)))",
						By(differenceFactorReal, translated))
					productReal := arg.Have(
						"and so is the product of the two factors",
						"real_measurable(set_cross(𝕌, 𝕌), "+
							"    «lebesgueProduct», "+
							"    λp:prod(real, real). normal_density(a, s, fst(p)) * normal_density(b + fst(p), t, snd(p)))",
						By(
							productSigma,
							firstFactorReal,
							secondFactorReal,
							measurable_function.RealMeasurableMul.At(pairs, lebesguePairs, firstFactor, secondFactor)))
					preimage := arg.Have(
						"the preimage of E under the second coordinate is measurable",
						"preimage_on(set_cross(𝕌, 𝕌), λp:prod(real, real). snd(p), E) ∈ «lebesgueProduct»",
						By(
							eBorel,
							secondBorelMap,
							measurable_space.MeasurableMapDef.At(pairs, lebesguePairs, line, borel, second)))
					cut := arg.Have(
						"that preimage is the set of pairs whose second coordinate lies in E",
						"preimage_on(set_cross(𝕌, 𝕌), λp:prod(real, real). snd(p), E) = {p:prod(real, real) | snd(p) ∈ E}",
						BySets(At(
							set_product.InCrossProjections.Inst(TypeBinder.BindA[Real](), TypeBinder.BindB[Real]()),
							line,
							line)))
					cutMeasurable := arg.Have(
						"so that set is measurable",
						"{p:prod(real, real) | snd(p) ∈ E} ∈ «lebesgueProduct»",
						By(preimage, cut))
					cutProduct := arg.Have(
						"the product cut to that set is measurable",
						"real_measurable(set_cross(𝕌, 𝕌), "+
							"    «lebesgueProduct», "+
							"    λp:prod(real, real). "+
							"        COND(p ∈ {p:prod(real, real) | snd(p) ∈ E}, "+
							"            normal_density(a, s, fst(p)) * normal_density(b + fst(p), t, snd(p)), "+
							"            &0))",
						By(
							productSigma,
							cutMeasurable,
							productReal,
							measurable_function.RealMeasurableOnEvent.At(pairs, lebesguePairs, cutEvent, product)))
					cutExtended := arg.Have(
						"and so is its embedding in the extended reals",
						"extended_measurable(set_cross(𝕌, 𝕌), "+
							"    «lebesgueProduct», "+
							"    λp:prod(real, real). "+
							"        extended_of_real(COND(p ∈ {p:prod(real, real) | snd(p) ∈ E}, "+
							"                normal_density(a, s, fst(p)) * normal_density(b + fst(p), t, snd(p)), "+
							"                &0)))",
						By(
							productSigma,
							cutProduct,
							measurable_function.ExtendedMeasurableOfReal.At(
								pairs,
								lebesguePairs,
								arg.TermAs[Fun[Prod[Real, Real], Real]](
									"λp:prod(real, real). "+
										"    COND(p ∈ {p:prod(real, real) | snd(p) ∈ E}, "+
										"        normal_density(a, s, fst(p)) * normal_density(b + fst(p), t, snd(p)), "+
										"        &0)"))))
					kernel := arg.Have(
						"the kernel is that embedded cut product",
						"(λp:prod(real, real). «densityKernel»(a, b, s, t, E, fst(p), snd(p))) = "+
							"λp:prod(real, real). "+
							"    extended_of_real(COND(p ∈ {p:prod(real, real) | snd(p) ∈ E}, "+
							"            normal_density(a, s, fst(p)) * normal_density(b + fst(p), t, snd(p)), "+
							"            &0))",
						Funext(),
						Derive(func(d *Argument) {
							d.FixAs[Prod[Real, Real]]("p")
							membership := d.Have(
								"membership in the cut set, read pointwise",
								"p ∈ {u:prod(real, real) | snd(u) ∈ E} ⇔ snd(p) ∈ E",
								BySets())
							nonnegative := d.Have(
								"the first density is nonnegative",
								"&0 ≤ normal_density(a, s, fst(p))",
								ByArith(sPositive, At(positiveDensity, a, s, d.TermAs[Real]("fst(p)"))))
							d.Show(
								"the embedding takes the nonnegative factor out of the cut",
								By(
									membership,
									nonnegative,
									At(
										embedCutProduct,
										d.TermAs[Real]("normal_density(a, s, fst(p))"),
										d.TermAs[Real]("normal_density(b + fst(p), t, snd(p))"),
										d.TermAs[Bool]("snd(p) ∈ E"))))
						}))
					arg.Show(
						"so the kernel is measurable on the plane",
						By(cutExtended, kernel))
				})

			exchangeIntegralOrder := ctx.Lemma(Statement{
				Binders: "∀a b s t:real. ∀E:set(real).",
				Hypotheses: []string{
					"&0 < s",
					"&0 < t",
					"E ∈ borel_sets(real_topology)",
				},
				Conclusion: "«lebesgueIntegral»( " +
					"    λx:real. «lebesgueIntegral»(λz:real. «densityKernel»(a, b, s, t, E, x, z))) = " +
					"«lebesgueIntegral»(λz:real. «lebesgueIntegral»(λx:real. «densityKernel»(a, b, s, t, E, x, z)))",
			},
				func(arg *Argument, a, b, s, t *Expr[Real], E *Expr[Set[Real]], sPositive, tPositive, eBorel Fact) {
					line := arg.TermAs[Set[Real]]("𝕌")
					lebesgue := arg.TermAs[Set[Set[Real]]]("«lebesgueSets»")
					outer := arg.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
						"lebesgue_outer_measure")
					kernel := arg.Have(
						"the density kernel is measurable on the plane",
						"extended_measurable(set_cross(𝕌, 𝕌), "+
							"    «lebesgueProduct», "+
							"    λp:prod(real, real). «densityKernel»(a, b, s, t, E, fst(p), snd(p)))",
						By(sPositive, tPositive, eBorel, At(jointKernelMeasurable, a, b, s, t, E)))
					arg.Show(
						"Tonelli: a nonnegative measurable kernel integrates in either order",
						By(
							kernel,
							lebesgue_measure.LebesgueSigmaFinite,
							product_measure.ProductNonnegIntegral.At(
								line,
								lebesgue,
								outer,
								line,
								lebesgue,
								outer,
								arg.TermAs[Fun2[Real, Real, extended_nonneg_real.ExtendedNonnegReal]](
									"λx:real. λz:real. "+
										"    extended_of_real(normal_density(a, s, x)) * "+
										"    COND(z ∈ E, extended_of_real(normal_density(b + x, t, z)), extended_of_real(&0))"))))
				})

			cutCommutesWithEmbedding := ctx.Lemma("∀r:real. ∀P:bool. "+
				"    extended_of_real(COND(P, r, &0)) = COND(P, extended_of_real(r), &0)",
				func(a *Argument, r *Expr[Real], P *Expr[Bool]) {
					a.Show(
						"on P both sides embed r, off P both are zero",
						BySets())
				})

			// At a fixed z the kernel, integrated over x, completes the square: the product of
			// the two densities is the density of N(a + b, s + t) at z times a normal density in
			// x, and the latter integrates to one.
			integrateCompletedSquare := ctx.Lemma(Statement{
				Binders: "∀a b s t z:real. ∀E:set(real).",
				Hypotheses: []string{
					"&0 < s",
					"&0 < t",
				},
				Conclusion: "«lebesgueIntegral»(λx:real. «densityKernel»(a, b, s, t, E, x, z)) = " +
					"«densityCut»(a + b, s + t, E, z)",
			},
				func(arg *Argument, a, b, s, t, z *Expr[Real], E *Expr[Set[Real]], sPositive, tPositive Fact) {
					line := arg.TermAs[Set[Real]]("𝕌")
					lebesgue := arg.TermAs[Set[Set[Real]]]("«lebesgueSets»")
					outer := arg.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
						"lebesgue_outer_measure")
					centre := arg.TermAs[Real]("a + s / (s + t) * (z - a - b)")
					variance := arg.TermAs[Real]("s * t / (s + t)")
					sum := arg.Have(
						"the variances add to a positive one",
						"&0 < s + t",
						ByArith(sPositive, tPositive))
					completedVariance := arg.Have(
						"the completed-square variance s·t/(s + t) is positive",
						"&0 < s * t / (s + t)",
						ByArith(sPositive, tPositive))
					cutNonnegative := arg.Have(
						"the density of the sum, cut to E, is nonnegative",
						"&0 ≤ COND(z ∈ E, normal_density(a + b, s + t, z), &0)",
						ByArith(sum, At(positiveDensity, arg.TermAs[Real]("a + b"), arg.TermAs[Real]("s + t"), z)))
					integrands := arg.Have(
						"the kernel is the cut density of the sum times a normal density in x",
						Statement{
							Binders: "∀x:real.",
							Hypotheses: []string{
								"x ∈ 𝕌",
							},
							Conclusion: "«densityKernel»(a, b, s, t, E, x, z) = " +
								"extended_of_real(COND(z ∈ E, normal_density(a + b, s + t, z), &0)) * " +
								"«density»(a + s / (s + t) * (z - a - b), s * t / (s + t), x)",
						},
						Derive(func(d *Argument) {
							x := d.FixAs[Real]("x")
							d.Assume()
							firstNonnegative := d.Have(
								"the first density is nonnegative",
								"&0 ≤ normal_density(a, s, x)",
								ByArith(sPositive, At(positiveDensity, a, s, x)))
							completedNonnegative := d.Have(
								"so is the completed-square density",
								"&0 ≤ normal_density(a + s / (s + t) * (z - a - b), s * t / (s + t), x)",
								ByArith(completedVariance, At(positiveDensity, centre, variance, x)))
							square := d.Have(
								"complete the square in the product of the densities",
								"normal_density(a, s, x) * normal_density(b + x, t, z) = "+
									"normal_density(a + b, s + t, z) * "+
									"normal_density(a + s / (s + t) * (z - a - b), s * t / (s + t), x)",
								By(sPositive, tPositive, NormalDensityConvolutionProduct.At(a, b, s, t, x, z)))
							commuted := d.Have(
								"with the factors in the other order",
								"normal_density(a, s, x) * normal_density(b + x, t, z) = "+
									"normal_density(a + s / (s + t) * (z - a - b), s * t / (s + t), x) * "+
									"normal_density(a + b, s + t, z)",
								ByArith(square))
							kernelCut := d.Have(
								"the kernel embeds the cut product of the densities",
								"«densityKernel»(a, b, s, t, E, x, z) = "+
									"extended_of_real(COND(z ∈ E, normal_density(a, s, x) * normal_density(b + x, t, z), &0))",
								By(
									firstNonnegative,
									At(
										embedCutProduct,
										d.TermAs[Real]("normal_density(a, s, x)"),
										d.TermAs[Real]("normal_density(b + x, t, z)"),
										d.TermAs[Bool]("z ∈ E"))))
							completedCut := d.Have(
								"the completed density times the cut density of the sum embeds their cut product",
								"«density»(a + s / (s + t) * (z - a - b), s * t / (s + t), x) * "+
									"«densityCut»(a + b, s + t, E, z) = "+
									"extended_of_real(COND(z ∈ E, "+
									"        normal_density(a + s / (s + t) * (z - a - b), s * t / (s + t), x) * "+
									"        normal_density(a + b, s + t, z), "+
									"        &0))",
								By(
									completedNonnegative,
									At(
										embedCutProduct,
										d.TermAs[Real]("normal_density(a + s / (s + t) * (z - a - b), s * t / (s + t), x)"),
										d.TermAs[Real]("normal_density(a + b, s + t, z)"),
										d.TermAs[Bool]("z ∈ E"))))
							embeddedCut := d.Have(
								"the cut commutes with the embedding",
								"«density»(a + s / (s + t) * (z - a - b), s * t / (s + t), x) * "+
									"extended_of_real(COND(z ∈ E, normal_density(a + b, s + t, z), &0)) = "+
									"extended_of_real(COND(z ∈ E, "+
									"        normal_density(a + s / (s + t) * (z - a - b), s * t / (s + t), x) * "+
									"        normal_density(a + b, s + t, z), "+
									"        &0))",
								By(
									completedCut,
									At(
										cutCommutesWithEmbedding,
										d.TermAs[Real]("normal_density(a + b, s + t, z)"),
										d.TermAs[Bool]("z ∈ E"))))
							factored := d.Have(
								"so the kernel is the completed density times the cut density of the sum",
								"«densityKernel»(a, b, s, t, E, x, z) = "+
									"«density»(a + s / (s + t) * (z - a - b), s * t / (s + t), x) * "+
									"extended_of_real(COND(z ∈ E, normal_density(a + b, s + t, z), &0))",
								By(kernelCut, embeddedCut, commuted))
							d.Show(
								"with the factors in the order of the claim",
								By(
									factored,
									extended_nonneg_real.MulComm.At(
										d.TermAs[extended_nonneg_real.ExtendedNonnegReal](
											"extended_of_real(normal_density(a + s / (s + t) * (z - a - b), s * t / (s + t), x))"),
										d.TermAs[extended_nonneg_real.ExtendedNonnegReal](
											"extended_of_real(COND(z ∈ E, normal_density(a + b, s + t, z), &0))"))))
						}))
					integral := arg.Have(
						"so the integrals over x agree",
						"«lebesgueIntegral»(λx:real. «densityKernel»(a, b, s, t, E, x, z)) = "+
							"«lebesgueIntegral»(λx:real. "+
							"        extended_of_real(COND(z ∈ E, normal_density(a + b, s + t, z), &0)) * "+
							"        «density»(a + s / (s + t) * (z - a - b), s * t / (s + t), x))",
						By(
							integrands,
							nonneg_integral.NonnegIntegralEqOn.At(
								line,
								lebesgue,
								outer,
								arg.TermAs[Fun[Real, extended_nonneg_real.ExtendedNonnegReal]](
									"λx:real. "+
										"    extended_of_real(normal_density(a, s, x)) * "+
										"    COND(z ∈ E, extended_of_real(normal_density(b + x, t, z)), extended_of_real(&0))"),
								arg.TermAs[Fun[Real, extended_nonneg_real.ExtendedNonnegReal]](
									"λx:real. "+
										"    extended_of_real(COND(z ∈ E, normal_density(a + b, s + t, z), &0)) * "+
										"    extended_of_real(normal_density(a + s / (s + t) * (z - a - b), s * t / (s + t), x))"))))
					scaled := arg.Have(
						"the nonnegative cut density of the sum comes out of the integral",
						"«lebesgueIntegral»(λx:real. "+
							"        extended_of_real(COND(z ∈ E, normal_density(a + b, s + t, z), &0)) * "+
							"        «density»(a + s / (s + t) * (z - a - b), s * t / (s + t), x)) = "+
							"extended_of_real(COND(z ∈ E, normal_density(a + b, s + t, z), &0)) * "+
							"«lebesgueIntegral»(λx:real. «density»(a + s / (s + t) * (z - a - b), s * t / (s + t), x))",
						By(
							cutNonnegative,
							lebesgue_measure.LebesgueMeasureOn,
							nonneg_integral.NonnegIntegralScale.At(
								line,
								lebesgue,
								outer,
								arg.TermAs[Fun[Real, extended_nonneg_real.ExtendedNonnegReal]](
									"λx:real. extended_of_real(normal_density(a + s / (s + t) * (z - a - b), s * t / (s + t), x))"),
								arg.TermAs[Real]("COND(z ∈ E, normal_density(a + b, s + t, z), &0)"))))
					unitMass := arg.Have(
						"the completed-square density has unit integral",
						"«lebesgueIntegral»(λx:real. «density»(a + s / (s + t) * (z - a - b), s * t / (s + t), x)) = "+
							"extended_of_real(&1)",
						By(completedVariance, At(normalDensityMassOne, centre, variance)))
					cutOfSum := arg.Have(
						"the embedded cut is the cut density of the sum",
						"extended_of_real(COND(z ∈ E, normal_density(a + b, s + t, z), &0)) = "+
							"«densityCut»(a + b, s + t, E, z)",
						By(
							At(
								cutCommutesWithEmbedding,
								arg.TermAs[Real]("normal_density(a + b, s + t, z)"),
								arg.TermAs[Bool]("z ∈ E"))))
					arg.Show(
						"the integral over x is the cut density of the sum",
						By(
							integral,
							scaled,
							unitMass,
							cutOfSum,
							extended_nonneg_real.MulOne.At(
								arg.TermAs[extended_nonneg_real.ExtendedNonnegReal](
									"extended_of_real(COND(z ∈ E, normal_density(a + b, s + t, z), &0))"))))
				})

			return ctx.Theorem(headline,
				func(arg *Argument, a, b, s, t *Expr[Real], E *Expr[Set[Real]], sPositive, tPositive, eBorel Fact) {
					inner := arg.Have(
						"at each z the inner integral of the kernel is the cut density of the sum",
						Statement{
							Binders: "∀z:real.",
							Hypotheses: []string{
								"z ∈ 𝕌",
							},
							Conclusion: "«lebesgueIntegral»(λx:real. «densityKernel»(a, b, s, t, E, x, z)) = " +
								"«densityCut»(a + b, s + t, E, z)",
						},
						Derive(func(d *Argument) {
							z := d.FixAs[Real]("z")
							d.Assume()
							d.Show(
								"complete the square at z",
								By(sPositive, tPositive, At(integrateCompletedSquare, a, b, s, t, z, E)))
						}))
					outer := arg.Have(
						"so the outer integrals over z agree",
						"«lebesgueIntegral»( "+
							"    λz:real. «lebesgueIntegral»(λx:real. «densityKernel»(a, b, s, t, E, x, z))) = "+
							"«lebesgueIntegral»(λz:real. «densityCut»(a + b, s + t, E, z))",
						By(
							inner,
							nonneg_integral.NonnegIntegralEqOn.At(
								arg.TermAs[Set[Real]]("𝕌"),
								arg.TermAs[Set[Set[Real]]]("«lebesgueSets»"),
								arg.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("lebesgue_outer_measure"),
								arg.TermAs[Fun[Real, extended_nonneg_real.ExtendedNonnegReal]](
									"λz:real. "+
										"    nonneg_integral(𝕌, "+
										"        {E:set(real) | lebesgue_measurable(E)}, "+
										"        lebesgue_outer_measure, "+
										"        λx:real. "+
										"            extended_of_real(normal_density(a, s, x)) * "+
										"            COND(z ∈ E, extended_of_real(normal_density(b + x, t, z)), extended_of_real(&0)))"),
								arg.TermAs[Fun[Real, extended_nonneg_real.ExtendedNonnegReal]](
									"λz:real. COND(z ∈ E, extended_of_real(normal_density(a + b, s + t, z)), extended_of_real(&0))"))))
					iterated := arg.Have(
						"the product mass is the iterated integral of the kernel, x outside",
						"«productMass»(a, b, s, t, E) = "+
							"«lebesgueIntegral»(λx:real. «lebesgueIntegral»(λz:real. «densityKernel»(a, b, s, t, E, x, z)))",
						By(sPositive, tPositive, eBorel, At(integrateXThenZ, a, b, s, t, E)))
					exchanged := arg.Have(
						"Tonelli puts z outside",
						"«lebesgueIntegral»( "+
							"    λx:real. «lebesgueIntegral»(λz:real. «densityKernel»(a, b, s, t, E, x, z))) = "+
							"«lebesgueIntegral»(λz:real. «lebesgueIntegral»(λx:real. «densityKernel»(a, b, s, t, E, x, z)))",
						By(sPositive, tPositive, eBorel, At(exchangeIntegralOrder, a, b, s, t, E)))
					sumMass := arg.Have(
						"the mass of E under the law of the sum is the integral of its cut density",
						"normal_distribution(a + b, s + t, E) = "+
							"«lebesgueIntegral»(λz:real. «densityCut»(a + b, s + t, E, z))",
						By(At(normalEventDensityIntegral, arg.TermAs[Real]("a + b"), arg.TermAs[Real]("s + t"), E)))
					arg.Show(
						"the product mass is the mass under the law of the sum",
						By(iterated, sumMass, exchanged, outer))
				})
		}),
})}
