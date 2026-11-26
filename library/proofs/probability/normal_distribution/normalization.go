package normal_distribution

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/borel_function"
	"github.com/euc-ai/xugo/library/proofs/measure/density_measure"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_integral"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_measure"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_riemann"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// normalDensityScaled — centering and scaling by the root of twice the variance leaves the Gaussian kernel.
var normalDensityScaled = normalDensityScaledThm{family.Add(registry.ProofEntry{
	Name: "normalDensityScaled",
	Key:  "prop_ef12e6d94793fec0",
	Build: family.Theorem(Statement{
		Binders:    "∀m v z:real.",
		Hypotheses: []string{"&0 < v"},
		Conclusion: "«scale» * normal_density(m, v, «point») = «kernel» / real_sqrt(pi)",
		Abbrev: Abbrev{
			{Name: "scale", Text: "real_sqrt(&2 * v)"},
			{Name: "denominator", Text: "real_sqrt(&2 * pi * v)"},
			{Name: "point", Text: "m + «scale» * z"},
			{Name: "kernel", Text: "real_exp(-real_pow(z, 2))"},
			{Name: "quotient", Text: "«kernel» / «denominator»"},
		},
	}, func(a *Argument, m, v, z *Expr[Real], positiveVariance Fact) {
		s := a.TermAs[Real]("«scale»")
		p := a.TermAs[Real]("real_sqrt(pi)")
		denominator := a.TermAs[Real]("«denominator»")
		kernel := a.TermAs[Real]("«kernel»")
		q := a.TermAs[Real]("«quotient»")
		twoV, pi := a.TermAs[Real]("&2 * v"), a.TermAs[Real]("pi")
		twoPiV := a.TermAs[Real]("&2 * pi * v")
		product := a.TermAs[Real]("«scale» * real_sqrt(pi)")
		power := a.TermAs[Nat]("2")
		squares := a.Have(
			"the two positive roots square to twice the variance and π",
			"&0 < «scale» ∧ "+
				"&0 < real_sqrt(pi) ∧ "+
				"real_pow(«scale», 2) = &2 * v ∧ "+
				"real_pow(real_sqrt(pi), 2) = pi",
			ByArith(
				positiveVariance,
				real_trigonometry.PiBounds,
				real_sqrt.SqrtPos.At(twoV),
				real_sqrt.SqrtPos.At(pi),
				real_sqrt.SqrtPowTwo.At(twoV),
				real_sqrt.SqrtPowTwo.At(pi)))
		root := a.Have(
			"the denominator is the product of the two positive roots",
			"«scale» * real_sqrt(pi) = «denominator»",
			ByArith(squares, real_pow.MulPowDistrib.At(s, p, power), real_sqrt.SqrtUnique.At(twoPiV, product)))
		shift := a.Have(
			"subtracting the mean leaves the scaled argument",
			"«point» - m = «scale» * z",
			ByArith())
		ratio := a.Have(
			"the exponent cancels twice the variance",
			"real_pow(«point» - m, 2) / (&2 * v) = real_pow(z, 2)",
			ByArith(
				shift,
				positiveVariance,
				squares,
				real_pow.MulPowDistrib.At(s, z, power),
				real_order_field.EqDivMulLeft.At(a.TermAs[Real]("real_pow(z, 2)"),
					a.TermAs[Real]("real_pow(«point» - m, 2)"), twoV)))
		cancel := a.Have(
			"multiplying the quotient by its positive denominator recovers the kernel",
			"«quotient» * «denominator» = «kernel»",
			ByArith(
				positiveVariance,
				real_trigonometry.PiBounds,
				real_sqrt.SqrtPos.At(twoPiV),
				real_order_field.EqDivMulLeft.At(q, kernel, denominator)))
		regroup := a.Have(
			"regroup the scale factors",
			"(«scale» * «quotient») * real_sqrt(pi) = «quotient» * («scale» * real_sqrt(pi))",
			ByArith())
		kernelProduct := a.Have(
			"the remaining root cancels the scaled quotient",
			"(«scale» * «quotient») * real_sqrt(pi) = «kernel»",
			By(root, cancel, regroup))
		a.Show(
			"the scaled density has only the normalization factor from π",
			Simp(Fwd(NormalDensityDef), Fwd(ratio)),
			By(
				kernelProduct,
				squares,
				real_order_field.EqDivMulLeft.At(a.TermAs[Real]("«scale» * «quotient»"), kernel, p)))
	}),
})}

// NormalDistributionProbability — the Gaussian density on the real line
// gives the Borel sets a measure of total mass one. The change of variables
// x = m + √(2v)·z (LebesgueNonnegIntegralAffineChange) turns the mass into
// 1/√π times the Gaussian integral √π.
var NormalDistributionProbability = normalDistributionProbabilityThm{family.Add(registry.ProofEntry{
	Name: "NormalDistributionProbability",
	Key:  "prop_71b56bb81a3cc94b",
	Reading: "0 < v is load-bearing: for v ≤ 0 the distribution is the zero measure. The Borel sets " +
		"are the σ-algebra named; the distribution is a measure on the Lebesgue measurable sets as well.",
	Build: family.Sections(Statement{
		Binders:    "∀m v:real.",
		Hypotheses: []string{"&0 < v"},
		Conclusion: "probability_on(𝕌, borel_sets(real_topology), normal_distribution(m, v))",
		Abbrev: Abbrev{
			{Name: "lebesgueSets", Text: "{E:set(real) | lebesgue_measurable(E)}"},
			{Name: "gaussian", Text: "λx:real. real_exp(-real_pow(x, 2))"},
			{Name: "embeddedGaussian", Text: "λx:real. extended_of_real(«gaussian»(x))"},
			{Name: "embeddedDensity", Text: "λx:real. extended_of_real(normal_density(m, v, x))"},
			{Name: "width", Text: "real_sqrt(&2 * v)"},
			{Name: "height", Text: "&1 / real_sqrt(pi)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		return ctx.Theorem(headline, func(a *Argument, m, v *Expr[Real], positiveVariance Fact) {
			carrier := a.TermAs[Set[Real]]("𝕌")
			borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
			lebesgue := a.TermAs[Set[Set[Real]]]("«lebesgueSets»")
			μ := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("lebesgue_outer_measure")
			ν := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("normal_distribution(m, v)")
			density := a.TermAs[Fun[Real, Real]]("normal_density(m, v)")
			gaussian := a.TermAs[Fun[Real, Real]]("«gaussian»")
			ρ := a.TermAs[Fun[Real, extended_nonneg_real.ExtendedNonnegReal]]("«embeddedDensity»")
			densityMeasure := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
				"density_measure(𝕌, «lebesgueSets», lebesgue_outer_measure, «embeddedDensity»)")
			width := a.TermAs[Real]("«width»")
			height := a.TermAs[Real]("«height»")
			pi := a.TermAs[Real]("pi")
			piRoot := a.TermAs[Real]("real_sqrt(pi)")
			zero, one := a.TermAs[Real]("&0"), a.TermAs[Real]("&1")
			roots := a.Have(
				"the roots used in the variance and normalization are positive",
				"&0 < «width» ∧ &0 < real_sqrt(&2 * pi * v) ∧ &0 < real_sqrt(pi)",
				ByArith(
					positiveVariance,
					real_trigonometry.PiBounds,
					real_sqrt.SqrtPos.At(a.TermAs[Real]("&2 * v")),
					real_sqrt.SqrtPos.At(a.TermAs[Real]("&2 * pi * v")),
					real_sqrt.SqrtPos.At(pi)))
			densityNonnegative := a.Have(
				"the exponential and its denominator are positive",
				"∀x:real. &0 ≤ normal_density(m, v, x)",
				Derive(func(b *Argument) {
					x := b.FixAs[Real]("x")
					b.Show(
						"the density is nonnegative at this point",
						ByArith(
							roots,
							NormalDensityDef.At(m, v, x),
							real_exp_log.ExpPositive.At(b.TermAs[Real]("-(real_pow(x - m, 2) / (&2 * v))"))))
				}))
			gaussianNonnegative := a.Have(
				"the exponential kernel is nonnegative",
				"∀x:real. &0 ≤ «gaussian»(x)",
				Derive(func(b *Argument) {
					b.FixAs[Real]("x")
					b.Show(
						"the exponential is positive",
						ByArith(real_exp_log.ExpPositive.At(b.TermAs[Real]("-real_pow(x, 2)"))))
				}))

			densityForm := a.Have(
				"write the density as a constant times an exponential of a shifted square",
				"normal_density(m, v) = "+
					"(λx:real. (&1 / real_sqrt(&2 * pi * v)) * real_exp(-(&1 / (&2 * v)) * ((x - m) * (x - m))))",
				Funext(),
				Simp(
					Fwd(NormalDensityDef),
					Fwd(real_pow.PowTwo),
					Fwd(real_field.RealDivDef),
					Fwd(real_construction.MulLeftId)),
				Derive(func(b *Argument) {
					b.FixAs[Real]("x")
					exponent := b.Have(
						"regroup the inverse and the square within the exponential",
						"-((x - m) * (x - m) * real_inv(&2 * v)) = -real_inv(&2 * v) * ((x - m) * (x - m))",
						ByArith())
					b.Show(
						"the same exponential occurs on both sides",
						Simp(Fwd(exponent)),
						ByArith())
				}))
			densityContinuous := a.Have(
				"the density is continuous on every set",
				"∀S:set(real). real_continuous_on(S, normal_density(m, v))",
				Derive(func(b *Argument) {
					S := b.FixAs[Set[Real]]("S")
					b.Show(
						"an exponential of a quadratic is continuous on the line, hence on S",
						By(
							densityForm,
							real_exp_log.ExponentialQuadraticContinuous.At(
								m, b.TermAs[Real]("-(&1 / (&2 * v))"), b.TermAs[Real]("&1 / real_sqrt(&2 * pi * v)")),
							set_order.SubsetUniv.At(S),
							real_continuous.ContinuousOnSubset.At(density, carrier, S)))
				}))
			inclusion := a.Have(
				"Borel sets are Lebesgue measurable",
				"borel_sets(real_topology) ⊆ «lebesgueSets»",
				BySets(lebesgue_measure.MeasurableBorel))
			measurable := a.Have(
				"a function continuous on the line is Lebesgue measurable",
				"real_measurable(𝕌, «lebesgueSets», normal_density(m, v))",
				By(densityContinuous.At(carrier), lebesgue_integral.ContinuousLebesgueMeasurable.At(density)))
			distribution := a.Have(
				"the distribution is the measure given by the embedded density",
				"normal_distribution(m, v) = "+
					"density_measure(𝕌, «lebesgueSets», lebesgue_outer_measure, «embeddedDensity»)",
				Funext(),
				Derive(func(b *Argument) {
					E := b.FixAs[Set[Real]]("E")
					b.Show(
						"read the density measure at this set",
						By(NormalDistributionDef.At(m, v, E)))
				}))
			lebesgueMeasure := a.Have(
				"a measurable density defines a measure on the Lebesgue sets",
				"measure_on(𝕌, "+
					"    «lebesgueSets», "+
					"    density_measure(𝕌, «lebesgueSets», lebesgue_outer_measure, «embeddedDensity»))",
				By(
					measurable,
					lebesgue_measure.LebesgueMeasureOn,
					lebesgue_measure.LebesgueSigmaAlgebra,
					measurable_function.ExtendedMeasurableOfReal.At(carrier, lebesgue, density),
					density_measure.DensityMeasure.At(carrier, lebesgue, μ, ρ)))
			measure := a.Have(
				"restrict the density measure to the Borel sets",
				"measure_on(𝕌, borel_sets(real_topology), normal_distribution(m, v))",
				By(
					distribution,
					borel_function.LineBorelSigmaAlgebra,
					inclusion,
					lebesgueMeasure,
					measure_space.SubSigmaMeasure.At(carrier, lebesgue, densityMeasure, borel)))
			mass := a.Have(
				"the mass of the line integrates the entire density",
				"normal_distribution(m, v, 𝕌) = "+
					"nonneg_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, «embeddedDensity»)",
				Simp(
					Fwd(NormalDistributionDef),
					Fwd(density_measure.DensityMeasureDef.Inst[Real]()),
					Fwd(set_basic.InUniv.Inst[Real]())),
				Basic())

			gaussianMass := a.Have(
				"the Gaussian integral has embedded value √π",
				"nonneg_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, «embeddedGaussian») = "+
					"extended_of_real(real_sqrt(pi))",
				By(
					gaussianNonnegative,
					lebesgue_riemann.GaussianIntegral,
					lebesgue_integral.LebesgueIntegrableIff.At(gaussian),
					lebesgue_integral.LebesgueIntegralEq.At(gaussian),
					measure_integral.IntegralNonnegEmbedding.At(carrier, lebesgue, μ, gaussian)))
			densityAffine := a.Have(
				"under x = m + «width»·z, «width» times the density is the scaled Gaussian kernel",
				"(λz:real. «width» * normal_density(m, v, m + «width» * z)) = (λz:real. «height» * «gaussian»(z))",
				Funext(),
				Derive(func(b *Argument) {
					z := b.FixAs[Real]("z")
					b.Show(
						"the exponent and denominator both simplify under the affine map",
						ByArith(positiveVariance, At(normalDensityScaled, m, v, z)))
				}))
			change := a.Have(
				"the change of variables x = m + «width»·z leaves the integral of the density as it is",
				"nonneg_integral(𝕌, "+
					"    «lebesgueSets», "+
					"    lebesgue_outer_measure, "+
					"    λz:real. extended_of_real(«width» * normal_density(m, v, m + «width» * z))) = "+
					"nonneg_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, «embeddedDensity»)",
				By(
					roots,
					densityNonnegative,
					densityContinuous.At(carrier),
					lebesgue_riemann.LebesgueNonnegIntegralAffineChange.At(density, m, width)))
			factor := a.Have(
				"the normalization factor is nonnegative and cancels √π",
				"&0 ≤ «height» ∧ «height» * real_sqrt(pi) = &1",
				ByArith(roots, real_order_field.EqDivMulLeft.At(height, one, piRoot)))
			split := a.Have(
				"the embedding splits the product of the nonnegative factor and the kernel",
				"(λz:real. extended_of_real(«height» * «gaussian»(z))) = "+
					"(λz:real. extended_of_real(«height») * «embeddedGaussian»(z))",
				Funext(),
				Derive(func(b *Argument) {
					z := b.FixAs[Real]("z")
					b.Show(
						"both factors are nonnegative",
						By(
							factor,
							gaussianNonnegative.At(z),
							extended_nonneg_real.OfRealMul.At(height, b.TermAs[Real]("«gaussian»(z)"))))
				}))
			scaled := a.Have(
				"the constant factor passes through the nonnegative integral",
				"nonneg_integral(𝕌, "+
					"    «lebesgueSets», "+
					"    lebesgue_outer_measure, "+
					"    λz:real. extended_of_real(«height») * «embeddedGaussian»(z)) = "+
					"extended_of_real(«height») * "+
					"nonneg_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, «embeddedGaussian»)",
				By(
					factor,
					lebesgue_measure.LebesgueMeasureOn,
					nonneg_integral.NonnegIntegralScale.At(
						carrier,
						lebesgue,
						μ,
						a.TermAs[Fun[Real, extended_nonneg_real.ExtendedNonnegReal]]("«embeddedGaussian»"),
						height)))
			unit := a.Have(
				"the normalizing factor times the Gaussian integral is one",
				"extended_of_real(«height») * extended_of_real(real_sqrt(pi)) = &1",
				By(
					factor,
					roots,
					extended_nonneg_real.OfRealMul.At(height, piRoot),
					real_order_ring.LessEqOfLessThan.At(zero, piRoot)))
			totalMass := a.Have(
				"change the variables, take the factor out and evaluate the Gaussian integral",
				"normal_distribution(m, v, 𝕌) = &1",
				By(mass, change, densityAffine, split, scaled, gaussianMass, unit))
			a.Show(
				"the Borel measure has total mass one",
				By(measure, totalMass, probability_space.ProbabilityOnDef.At(carrier, borel, ν)))
		})
	}),
})}
