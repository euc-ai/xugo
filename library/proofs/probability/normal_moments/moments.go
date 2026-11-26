package normal_moments

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/borel_function"
	"github.com/euc-ai/xugo/library/proofs/measure/density_measure"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/probability/normal_distribution"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_integral"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_measure"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_riemann"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// NormalDistributionMoments — under normal_distribution(m, v) the identity
// has mean m and variance v, its square integrable. The standard normal's
// moments are computed on the windows ⟦−n, n⟧ of its density φ, the sections
// standardDensitySections proves below: −φ is a primitive of y·φ(y),
// so the first moment's windows vanish and integration by parts makes the
// second moment's windows those of φ less 2n·φ(n), which tends to 0; the
// affine change y ↦ m + √v·y carries them to mean m and variance v.
var NormalDistributionMoments = normalDistributionMomentsThm{family.Add(registry.ProofEntry{
	Name: "NormalDistributionMoments",
	Key:  "prop_4cdb0aab5b7e0f37",
	Reading: "The variable is the identity on the line, whose distribution under " +
		"normal_distribution(m, v) is that measure: the mean is m and the variance v.",
	Build: family.Sections(Statement{
		Binders: "∀m v:real.",
		Hypotheses: []string{
			"&0 < v",
		},
		Conclusion: "real_integrable(𝕌, " +
			"    borel_sets(real_topology), " +
			"    normal_distribution(m, v), " +
			"    λx:real. x * x) ∧ " +
			"expectation(𝕌, borel_sets(real_topology), normal_distribution(m, v), λx:real. x) = m ∧ " +
			"variance(𝕌, borel_sets(real_topology), normal_distribution(m, v), λx:real. x) = v",
		Abbrev: Abbrev{
			{Name: "lebesgueSets", Text: "{E:set(real) | lebesgue_measurable(E)}"},
			{Name: "densityMeasure", Text: "density_measure(𝕌, " +
				"    «lebesgueSets», " +
				"    lebesgue_outer_measure, " +
				"    λx:real. extended_of_real(normal_density(&0, &1, x)))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		std := standardDensitySections(ctx)
		firstWindow := ctx.Lemma(Statement{
			Binders: "∀R:real.",
			Hypotheses: []string{
				"&0 ≤ R",
			},
			Conclusion: "real_integral(λy:real. y * normal_density(&0, &1, y), -R, R) = &0",
		}, func(a *Argument, R *Expr[Real], radius Fact) {
			window := a.TermAs[Set[Real]]("⟦-R, R⟧")
			weighted := a.TermAs[Fun[Real, Real]]("λy:real. y * normal_density(&0, &1, y)")
			order := a.Have(
				"the window is ordered",
				"-R ≤ R",
				ByArith(radius))
			increment := a.Have(
				"−φ is a primitive of y·φ(y), so the window integral is its increment",
				"real_has_integral(λy:real. y * normal_density(&0, &1, y), "+
					"    -R, "+
					"    R, "+
					"    -normal_density(&0, &1, R) - -normal_density(&0, &1, -R))",
				By(
					order,
					At(std.continuous, window),
					real_continuous.ContinuousOnNeg.At(a.TermAs[Fun[Real, Real]]("normal_density(&0, &1)"), window),
					At(std.weightedContinuous, window),
					std.negativeDerivative,
					real_integral.NewtonLeibnizContinuous.At(
						a.TermAs[Fun[Real, Real]]("λy:real. -normal_density(&0, &1, y)"),
						weighted,
						a.TermAs[Real]("-R"),
						R)))
			a.Show(
				"φ is even, so the increment vanishes",
				ByArith(
					increment,
					At(std.even, R),
					real_integral.HasIntegralValue.At(
						weighted,
						a.TermAs[Real]("-R"),
						R,
						a.TermAs[Real]("-normal_density(&0, &1, R) - -normal_density(&0, &1, -R)"))))
		})
		squareWindow := ctx.Lemma(Statement{
			Binders: "∀R:real.",
			Hypotheses: []string{
				"&0 ≤ R",
			},
			Conclusion: "real_integral(λy:real. y * y * normal_density(&0, &1, y), -R, R) = " +
				"real_integral(normal_density(&0, &1), -R, R) - &2 * R * normal_density(&0, &1, R)",
		}, func(a *Argument, R *Expr[Real], radius Fact) {
			window := a.TermAs[Set[Real]]("⟦-R, R⟧")
			left := a.TermAs[Real]("-R")
			density := a.TermAs[Fun[Real, Real]]("normal_density(&0, &1)")
			negated := a.TermAs[Fun[Real, Real]]("λy:real. -normal_density(&0, &1, y)")
			mass := a.TermAs[Real]("real_integral(normal_density(&0, &1), -R, R)")
			order := a.Have(
				"the window is ordered",
				"-R ≤ R",
				ByArith(radius))
			slopes := a.Have(
				"y has derivative 1 and −φ has derivative y·φ(y)",
				Statement{
					Binders:    "∀x:real.",
					Hypotheses: []string{"-R ≤ x", "x ≤ R"},
					Conclusion: "real_derivative_at(λy:real. y, x, &1) ∧ " +
						"real_derivative_at(λy:real. -normal_density(&0, &1, y), x, x * normal_density(&0, &1, x))",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[Real]("x")
					b.Assume()
					b.Show(
						"the identity's derivative, and the section on −φ",
						By(real_derivative.DerivativeId.At(x), At(std.negativeDerivative, x)))
				}))
			integrand := a.Have(
				"y²·φ(y) is y times y·φ(y)",
				"(λx:real. x * (x * normal_density(&0, &1, x))) = (λy:real. y * y * normal_density(&0, &1, y))",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[Real]("x")
					b.Show(
						"regroup the product",
						ByArith())
				}))
			parts := a.Have(
				"integrate y·(y·φ(y)) by parts, −φ being a primitive of y·φ(y)",
				"real_integral(λy:real. y * y * normal_density(&0, &1, y), -R, R) = "+
					"R * -normal_density(&0, &1, R) - "+
					"-R * -normal_density(&0, &1, -R) - "+
					"real_integral(λx:real. &1 * -normal_density(&0, &1, x), -R, R)",
				By(
					order,
					slopes,
					integrand,
					real_continuous.ContinuousOnConst.At(a.TermAs[Real]("&1"), window),
					At(std.weightedContinuous, window),
					real_integral.IntegrationByParts.At(
						a.TermAs[Fun[Real, Real]]("λy:real. y"),
						a.TermAs[Fun[Real, Real]]("λy:real. &1"),
						negated,
						a.TermAs[Fun[Real, Real]]("λy:real. y * normal_density(&0, &1, y)"),
						left,
						R)))
			remainder := a.Have(
				"the remaining integrand is −φ, whose integral is −∫φ",
				"real_integral(λx:real. &1 * -normal_density(&0, &1, x), -R, R) = "+
					"-real_integral(normal_density(&0, &1), -R, R)",
				ByArith(
					order,
					At(std.continuous, window),
					real_integral.ContinuousHasIntegral.At(density, left, R),
					real_integral.HasIntegralNeg.At(density, left, R, mass),
					real_integral.RiemannIntegralScale.At(
						negated,
						left,
						R,
						a.TermAs[Real]("-real_integral(normal_density(&0, &1), -R, R)"),
						a.TermAs[Real]("&1")),
					real_integral.HasIntegralValue.At(
						negated, left, R, a.TermAs[Real]("-real_integral(normal_density(&0, &1), -R, R)"))))
			a.Show(
				"φ is even, so the boundary terms are −2R·φ(R)",
				ByArith(parts, remainder, At(std.even, R)))
		})
		scaledBoundary := ctx.Lemma("∀x:real. "+
			"    x * (&2 * x * normal_density(&0, &1, x)) ≤ &4 * (&1 / real_sqrt(&2 * π))",
			func(a *Argument, x *Expr[Real]) {
				half := a.TermAs[Real]("x * x / &2")
				bound := a.TermAs[Real]("&4 * (&1 / real_sqrt(&2 * π))")
				kernel := a.Have(
					"t·e^{−t} ≤ 1 at t = x²/2",
					"x * x / &2 * exp(-(x * x / &2)) ≤ &1",
					ByArith(real_exp_log.ExpNegMulBound.At(half)))
				positive := a.Have(
					"4/√(2π) is positive",
					"&0 ≤ &4 * (&1 / real_sqrt(&2 * π))",
					ByArith(
						real_trigonometry.PiBounds,
						real_sqrt.SqrtPos.At(a.TermAs[Real]("&2 * π")),
						real_order_field.DivPos.At(a.TermAs[Real]("&1"), a.TermAs[Real]("real_sqrt(&2 * π)"))))
				a.Show(
					"x·2x·φ(x) is 4/√(2π) times (x²/2)·e^{−x²/2}",
					Simp(Fwd(std.formula)),
					ByArith(
						kernel,
						positive,
						real_order_ring.LessEqMulLeft.At(
							bound, a.TermAs[Real]("x * x / &2 * exp(-(x * x / &2))"), a.TermAs[Real]("&1"))))
			})
		boundaryVanishes := ctx.Lemma("(λn:num. &2 * &n * normal_density(&0, &1, &n)) ⟶ &0",
			func(a *Argument) {
				bound := a.TermAs[Real]("&4 * (&1 / real_sqrt(&2 * π))")
				a.Show(
					"for ε > 0, past an N with 4/√(2π) < N·ε the term is below ε",
					Simp(Fwd(real_sequences.RealConvergesToDef)),
					Derive(func(b *Argument) {
						ε := b.FixAs[Real]("ε")
						positive := b.Assume()
						N, large := b.ObtainAs[Nat](
							"N exists by the Archimedean property",
							"∃N:num. &4 * (&1 / real_sqrt(&2 * π)) < &N * ε",
							By(positive, real_archimedean.Archimedean.At(ε, bound)))
						b.Show(
							"this N serves",
							Witness(N),
							Derive(func(c *Argument) {
								n := c.FixAs[Nat]("n")
								past := c.Assume()
								index := c.TermAs[Real]("&n")
								term := c.TermAs[Real]("&2 * &n * normal_density(&0, &1, &n)")
								nonnegative := c.Have(
									"n is nonnegative",
									"&0 ≤ &n",
									By(real_order_ring.NumNonneg.At(n)))
								grows := c.Have(
									"ε·N ≤ ε·n",
									"ε * &N ≤ ε * &n",
									ByArith(
										past,
										positive,
										real_construction.OfNumLessEq.At(N, n),
										real_order_ring.LessEqMulLeft.At(ε, c.TermAs[Real]("&N"), index)))
								scaled := c.Have(
									"n·(2n·φ(n)) ≤ 4/√(2π) < N·ε ≤ n·ε",
									"&n * (&2 * &n * normal_density(&0, &1, &n)) < &n * ε",
									ByArith(grows, large, At(scaledBoundary, index)))
								termNonnegative := c.Have(
									"the term is nonnegative, so its distance from 0 is itself",
									"|&2 * &n * normal_density(&0, &1, &n) - &0| = &2 * &n * normal_density(&0, &1, &n)",
									ByArith(nonnegative, At(std.nonnegative, index), real_sgn_abs.AbsFixedIffNonneg.At(term)))
								c.Cases(c.TermAs[Bool]("&n = &0"))
								c.When(
									"at n = 0 the term is 0",
									func(d *Argument, zero Fact) {
										d.Show(
											"which is below ε",
											ByArith(zero, positive, termNonnegative))
									})
								c.Otherwise(
									"otherwise n is positive and cancels from both sides",
									func(d *Argument, nonzero Fact) {
										positiveIndex := d.Have(
											"n is positive",
											"&0 < &n",
											ByArith(nonzero, nonnegative))
										d.Show(
											"so the term is below ε",
											ByArith(positiveIndex, scaled, termNonnegative))
									})
							}))
					}))
			})
		densityWindows := ctx.Lemma("(λn:num. real_integral(normal_density(&0, &1), -&n, &n)) ⟶ &1",
			func(a *Argument) {
				line := a.TermAs[Set[Real]]("𝕌")
				borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
				law := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
					"normal_distribution(&0, &1)")
				density := a.TermAs[Fun[Real, Real]]("normal_density(&0, &1)")
				zero, one := a.TermAs[Real]("&0"), a.TermAs[Real]("&1")
				total := a.Have(
					"the standard normal gives the line mass one",
					"normal_distribution(&0, &1, 𝕌) = &1",
					By(
						normal_distribution.NormalDistributionProbability.At(zero, one),
						probability_space.ProbabilityOnDef.At(line, borel, law)))
				mass := a.Have(
					"that mass is the nonnegative integral of φ over the line",
					"normal_distribution(&0, &1, 𝕌) = "+
						"nonneg_integral(𝕌, "+
						"    «lebesgueSets», "+
						"    lebesgue_outer_measure, "+
						"    λx:real. extended_of_real(normal_density(&0, &1, x)))",
					Simp(
						Fwd(normal_distribution.NormalDistributionDef),
						Fwd(density_measure.DensityMeasureDef.Inst[Real]()),
						Fwd(set_basic.InUniv.Inst[Real]())),
					Basic())
				a.Show(
					"the windows of φ increase to that integral, so their limit is one",
					ByArith(
						total,
						mass,
						At(std.windows, density),
						At(std.continuous, line),
						std.nonnegative,
						extended_nonneg_real.SupSequenceOfReal.At(
							a.TermAs[Fun[Nat, Real]]("λn:num. real_integral(normal_density(&0, &1), -&n, &n)"), one)))
			})
		squareWindows := ctx.Lemma("(λn:num. "+
			"    real_integral(λy:real. y * y * normal_density(&0, &1, y), -&n, &n)) ⟶ "+
			"&1",
			func(a *Argument) {
				windows := a.Have(
					"each window of y²·φ(y) is that of φ less the boundary term 2n·φ(n)",
					"(λn:num. real_integral(λy:real. y * y * normal_density(&0, &1, y), -&n, &n)) = "+
						"(λn:num. real_integral(normal_density(&0, &1), -&n, &n) - &2 * &n * normal_density(&0, &1, &n))",
					Funext(),
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.Show(
							"the window identity at radius n",
							By(real_order_ring.NumNonneg.At(n), At(squareWindow, b.TermAs[Real]("&n"))))
					}))
				a.Show(
					"the windows of φ tend to 1 and the boundary term to 0",
					By(
						windows,
						densityWindows,
						boundaryVanishes,
						real_sequences.LimitSub.At(
							a.TermAs[Fun[Nat, Real]]("λn:num. real_integral(normal_density(&0, &1), -&n, &n)"),
							a.TermAs[Fun[Nat, Real]]("λn:num. &2 * &n * normal_density(&0, &1, &n)"),
							a.TermAs[Real]("&1"),
							a.TermAs[Real]("&0")),
						real_ring.SubRightZero.At(a.TermAs[Real]("&1"))))
			})
		secondMoment := ctx.Lemma("real_integrable(𝕌, "+
			"    borel_sets(real_topology), "+
			"    normal_distribution(&0, &1), "+
			"    λx:real. x * x) ∧ "+
			"expectation(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λx:real. x * x) = &1",
			func(a *Argument) {
				line := a.TermAs[Set[Real]]("𝕌")
				weighted := a.TermAs[Fun[Real, Real]]("λy:real. y * y * normal_density(&0, &1, y)")
				nonnegative := a.Have(
					"y²·φ(y) is nonnegative",
					"∀x:real. &0 ≤ x * x * normal_density(&0, &1, x)",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]("x")
						b.Show(
							"a square times a nonnegative density",
							ByArith(At(std.nonnegative, x)))
					}))
				lebesgue := a.Have(
					"its windows tend to 1, so y²·φ(y) is Lebesgue integrable with integral 1",
					"real_integrable(𝕌, "+
						"    «lebesgueSets», "+
						"    lebesgue_outer_measure, "+
						"    λy:real. y * y * normal_density(&0, &1, y)) ∧ "+
						"measure_integral(𝕌, "+
						"    «lebesgueSets», "+
						"    lebesgue_outer_measure, "+
						"    λy:real. y * y * normal_density(&0, &1, y)) = "+
						"&1",
					By(
						nonnegative,
						At(std.weightedContinuous, line),
						squareWindows,
						lebesgue_riemann.LebesgueIntegralByCenteredWindows.At(weighted, a.TermAs[Real]("&1"))))
				integrand := a.Have(
					"φ times the square is y²·φ(y)",
					"(λy:real. y * y * normal_density(&0, &1, y)) = (λx:real. normal_density(&0, &1, x) * (x * x))",
					Funext(),
					Derive(func(b *Argument) {
						b.FixAs[Real]("y")
						b.Show(
							"commute the product",
							ByArith())
					}))
				a.Show(
					"the square is Borel, so its expectation is that Lebesgue integral",
					By(
						integrand,
						lebesgue,
						std.powersMeasurable,
						At(std.transport, a.TermAs[Fun[Real, Real]]("λx:real. x * x"))))
			})
		subtraction := ctx.Lemma(Statement{
			Binders: "∀f g:(real → real). ∀a b:real.",
			Hypotheses: []string{
				"a ≤ b",
				"real_continuous_on(⟦a, b⟧, f)",
				"real_continuous_on(⟦a, b⟧, g)",
			},
			Conclusion: "real_integral(λx:real. f(x) - g(x), a, b) = " +
				"real_integral(f, a, b) - real_integral(g, a, b)",
		}, func(
			arg *Argument,
			f, g *Arrow[Real, Real],
			a, b *Expr[Real],
			order, fContinuous, gContinuous Fact,
		) {
			fIntegral := arg.TermAs[Real]("real_integral(f, a, b)")
			gIntegral := arg.TermAs[Real]("real_integral(g, a, b)")
			arg.Show(
				"both have their integrals, and the difference integrates to the difference",
				By(
					order,
					fContinuous,
					gContinuous,
					real_integral.ContinuousHasIntegral.At(f, a, b),
					real_integral.ContinuousHasIntegral.At(g, a, b),
					real_integral.HasIntegralSub.At(f, g, a, b, fIntegral, gIntegral),
					real_integral.HasIntegralValue.At(
						arg.TermAs[Fun[Real, Real]]("λx:real. f(x) - g(x)"),
						a,
						b,
						arg.TermAs[Real]("real_integral(f, a, b) - real_integral(g, a, b)"))))
		})
		balancedWindows := ctx.Lemma(Statement{
			Binders: "∀f:(real → real).",
			Hypotheses: []string{
				"real_continuous_on(𝕌, f)",
				"∀n:num. real_integral(f, -&n, &n) = &0",
			},
			Conclusion: "measure_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, f) = &0",
		}, func(a *Argument, f *Arrow[Real, Real], continuous, balanced Fact) {
			line := a.TermAs[Set[Real]]("𝕌")
			lebesgue := a.TermAs[Set[Set[Real]]]("«lebesgueSets»")
			μ := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("lebesgue_outer_measure")
			positivePart := a.TermAs[Fun[Real, Real]]("λx:real. max(f(x), &0)")
			negativePart := a.TermAs[Fun[Real, Real]]("λx:real. max(-f(x), &0)")
			nonnegative := a.Have(
				"the positive and negative parts are nonnegative",
				"(∀x:real. &0 ≤ max(f(x), &0)) ∧ (∀x:real. &0 ≤ max(-f(x), &0))",
				ByArith())
			halves := a.Have(
				"each part is half of |f| ± f",
				"(λx:real. max(f(x), &0)) = (λx:real. (|f(x)| + f(x)) * (&1 / &2)) ∧ "+
					"(λx:real. max(-f(x), &0)) = (λx:real. (|f(x)| - f(x)) * (&1 / &2))",
				SplitConj(
					Case(
						"the positive part is (|f| + f)/2",
						Funext(),
						Derive(func(b *Argument) {
							b.FixAs[Real]("x")
							b.Show(
								"by the sign of f(x)",
								ByArith())
						})),
					Case(
						"the negative part is (|f| − f)/2",
						Funext(),
						Derive(func(b *Argument) {
							b.FixAs[Real]("x")
							b.Show(
								"by the sign of f(x)",
								ByArith())
						}))))
			absolute := a.TermAs[Fun[Real, Real]]("λx:real. |f(x)|")
			half := a.TermAs[Fun[Real, Real]]("λx:real. &1 / &2")
			partsContinuous := a.Have(
				"so both parts are continuous",
				"real_continuous_on(𝕌, λx:real. max(f(x), &0)) ∧ real_continuous_on(𝕌, λx:real. max(-f(x), &0))",
				By(
					halves,
					continuous,
					real_continuous.ContinuousOnAbs.At(f, line),
					real_continuous.ContinuousOnAdd.At(absolute, f, line),
					real_continuous.ContinuousOnSub.At(absolute, f, line),
					real_continuous.ContinuousOnConst.At(a.TermAs[Real]("&1 / &2"), line),
					real_continuous.ContinuousOnMul.At(a.TermAs[Fun[Real, Real]]("λx:real. |f(x)| + f(x)"), half, line),
					real_continuous.ContinuousOnMul.At(
						a.TermAs[Fun[Real, Real]]("λx:real. |f(x)| - f(x)"), half, line)))
			equalWindows := a.Have(
				"f⁺ − f⁻ = f, whose windows vanish, so f⁺ and f⁻ have equal windows",
				"(λn:num. extended_of_real(real_integral(λx:real. max(f(x), &0), -&n, &n))) = "+
					"(λn:num. extended_of_real(real_integral(λx:real. max(-f(x), &0), -&n, &n)))",
				Funext(),
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					window := b.TermAs[Set[Real]]("⟦-&n, &n⟧")
					difference := b.Have(
						"the difference of the parts is f",
						"(λx:real. max(f(x), &0) - max(-f(x), &0)) = f",
						Funext(),
						Derive(func(c *Argument) {
							c.FixAs[Real]("x")
							c.Show(
								"by the sign of f(x)",
								ByArith())
						}))
					b.Show(
						"subtract the window integrals",
						ByArith(
							difference,
							balanced.At(n),
							partsContinuous,
							real_order_ring.NumNonneg.At(n),
							set_order.SubsetUniv.At(window),
							real_continuous.ContinuousOnSubset.At(positivePart, line, window),
							real_continuous.ContinuousOnSubset.At(negativePart, line, window),
							At(subtraction, positivePart, negativePart, b.TermAs[Real]("-&n"), b.TermAs[Real]("&n"))))
				}))
			equalMasses := a.Have(
				"so f⁺ and f⁻ have one nonnegative integral, the supremum of their windows",
				"nonneg_integral(𝕌, "+
					"    «lebesgueSets», "+
					"    lebesgue_outer_measure, "+
					"    λx:real. extended_of_real(max(f(x), &0))) = "+
					"nonneg_integral(𝕌, "+
					"    «lebesgueSets», "+
					"    lebesgue_outer_measure, "+
					"    λx:real. extended_of_real(max(-f(x), &0)))",
				By(
					equalWindows,
					nonnegative,
					partsContinuous,
					At(std.windows, positivePart),
					At(std.windows, negativePart)))
			embedded := a.Have(
				"f and −f embed as their positive parts",
				"(λx:real. extended_of_real(f(x))) = (λx:real. extended_of_real(max(f(x), &0))) ∧ "+
					"(λx:real. extended_of_real(-f(x))) = (λx:real. extended_of_real(max(-f(x), &0)))",
				SplitConj(
					Case(
						"f embeds as its positive part",
						Funext(),
						Derive(func(b *Argument) {
							x := b.FixAs[Real]("x")
							b.Show(
								"the embedding cuts at 0",
								By(extended_nonneg_real.OfRealPositivePart.At(f.Apply(x))))
						})),
					Case(
						"−f embeds as the negative part of f",
						Funext(),
						Derive(func(b *Argument) {
							b.FixAs[Real]("x")
							b.Show(
								"the embedding cuts at 0",
								By(extended_nonneg_real.OfRealPositivePart.At(b.TermAs[Real]("-f(x)"))))
						}))))
			a.Show(
				"the integral of f is the difference of the two equal masses",
				ByArith(equalMasses, embedded, measure_integral.RealIntegralDef.At(line, lebesgue, μ, f)))
		})
		firstMoment := ctx.Lemma("real_integrable(𝕌, "+
			"    borel_sets(real_topology), "+
			"    normal_distribution(&0, &1), "+
			"    λx:real. x) ∧ "+
			"expectation(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λx:real. x) = &0",
			func(a *Argument) {
				line := a.TermAs[Set[Real]]("𝕌")
				borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
				law := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
					"normal_distribution(&0, &1)")
				zero, one := a.TermAs[Real]("&0"), a.TermAs[Real]("&1")
				identity := a.TermAs[Fun[Real, Real]]("λx:real. x")
				weighted := a.TermAs[Fun[Real, Real]]("λx:real. x * normal_density(&0, &1, x)")
				integrable := a.Have(
					"x² is integrable under the standard normal, a probability, so x is integrable",
					"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λx:real. x)",
					By(
						normal_distribution.NormalDistributionProbability.At(zero, one),
						std.powersMeasurable,
						secondMoment,
						probability_space.SquareIntegrableIntegrable.At(line, borel, law, identity)))
				vanishing := a.Have(
					"every window of x·φ(x) integrates to 0",
					"∀n:num. real_integral(λx:real. x * normal_density(&0, &1, x), -&n, &n) = &0",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.Show(
							"the first window identity at radius n",
							By(real_order_ring.NumNonneg.At(n), At(firstWindow, b.TermAs[Real]("&n"))))
					}))
				lebesgue := a.Have(
					"so x·φ(x) has Lebesgue integral 0",
					"measure_integral(𝕌, "+
						"    «lebesgueSets», "+
						"    lebesgue_outer_measure, "+
						"    λx:real. x * normal_density(&0, &1, x)) = "+
						"&0",
					By(vanishing, At(std.weightedContinuous, line), At(balancedWindows, weighted)))
				integrand := a.Have(
					"φ times x is x·φ(x)",
					"(λx:real. x * normal_density(&0, &1, x)) = (λx:real. normal_density(&0, &1, x) * x)",
					Funext(),
					Derive(func(b *Argument) {
						b.FixAs[Real]("x")
						b.Show(
							"commute the product",
							ByArith())
					}))
				a.Show(
					"the identity is Borel, so its expectation is that Lebesgue integral",
					By(integrand, lebesgue, integrable, std.powersMeasurable, At(std.transport, identity)))
			})
		quadraticMoment := ctx.Lemma("∀a b c:real. "+
			"    real_integrable(𝕌, "+
			"        borel_sets(real_topology), "+
			"        normal_distribution(&0, &1), "+
			"        λx:real. a + b * x + c * (x * x)) ∧ "+
			"    expectation(𝕌, "+
			"        borel_sets(real_topology), "+
			"        normal_distribution(&0, &1), "+
			"        λx:real. a + b * x + c * (x * x)) = "+
			"    a + c",
			func(arg *Argument, a, b, c *Expr[Real]) {
				line := arg.TermAs[Set[Real]]("𝕌")
				borel := arg.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
				law := arg.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
					"normal_distribution(&0, &1)")
				identity := arg.TermAs[Fun[Real, Real]]("λx:real. x")
				square := arg.TermAs[Fun[Real, Real]]("λx:real. x * x")
				constant := arg.TermAs[Fun[Real, Real]]("λx:real. a")
				linear := arg.TermAs[Fun[Real, Real]]("λx:real. b * x")
				affine := arg.TermAs[Fun[Real, Real]]("λx:real. a + b * x")
				quadratic := arg.TermAs[Fun[Real, Real]]("λx:real. c * (x * x)")
				probability := arg.Have(
					"the standard normal is a probability measure",
					"probability_on(𝕌, borel_sets(real_topology), normal_distribution(&0, &1)) ∧ "+
						"measure_on(𝕌, borel_sets(real_topology), normal_distribution(&0, &1))",
					By(
						normal_distribution.NormalDistributionProbability.At(
							arg.TermAs[Real]("&0"), arg.TermAs[Real]("&1")),
						probability_space.ProbabilityOnDef.At(line, borel, law)))
				moments := arg.Have(
					"the constant a, x and x² have integrals a, 0 and 1",
					"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λx:real. a) ∧ "+
						"measure_integral(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λx:real. a) = a ∧ "+
						"measure_integral(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λx:real. x) = &0 ∧ "+
						"measure_integral(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λx:real. x * x) = &1",
					By(
						probability,
						firstMoment,
						secondMoment,
						probability_space.ExpectationConstant.At(line, borel, law, a),
						probability_space.ExpectationDef.At(line, borel, law, constant),
						probability_space.ExpectationDef.At(line, borel, law, identity),
						probability_space.ExpectationDef.At(line, borel, law, square)))
				scaled := arg.Have(
					"b·x and c·x² are integrable, with integrals 0 and c",
					"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λx:real. b * x) ∧ "+
						"measure_integral(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λx:real. b * x) = "+
						"&0 ∧ "+
						"real_integrable(𝕌, "+
						"    borel_sets(real_topology), "+
						"    normal_distribution(&0, &1), "+
						"    λx:real. c * (x * x)) ∧ "+
						"measure_integral(𝕌, "+
						"    borel_sets(real_topology), "+
						"    normal_distribution(&0, &1), "+
						"    λx:real. c * (x * x)) = "+
						"c",
					ByArith(
						probability,
						moments,
						firstMoment,
						secondMoment,
						measure_integral.IntegrableScale.At(line, borel, law, identity, b),
						measure_integral.IntegralScale.At(line, borel, law, identity, b),
						measure_integral.IntegrableScale.At(line, borel, law, square, c),
						measure_integral.IntegralScale.At(line, borel, law, square, c)))
				sum := arg.Have(
					"a + b·x is integrable with integral a",
					"real_integrable(𝕌, "+
						"    borel_sets(real_topology), "+
						"    normal_distribution(&0, &1), "+
						"    λx:real. a + b * x) ∧ "+
						"measure_integral(𝕌, "+
						"    borel_sets(real_topology), "+
						"    normal_distribution(&0, &1), "+
						"    λx:real. a + b * x) = "+
						"a",
					ByArith(
						probability,
						moments,
						scaled,
						measure_integral.IntegrableAdd.At(line, borel, law, constant, linear),
						measure_integral.IntegralAdd.At(line, borel, law, constant, linear)))
				arg.Show(
					"adding c·x² adds c",
					Simp(Fwd(probability_space.ExpectationDef)),
					ByArith(
						probability,
						sum,
						scaled,
						measure_integral.IntegrableAdd.At(line, borel, law, affine, quadratic),
						measure_integral.IntegralAdd.At(line, borel, law, affine, quadratic)))
			})
		return ctx.Theorem(headline, func(a *Argument, m, v *Expr[Real], positive Fact) {
			line := a.TermAs[Set[Real]]("𝕌")
			borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
			identity := a.TermAs[Fun[Real, Real]]("λx:real. x")
			square := a.TermAs[Fun[Real, Real]]("λx:real. x * x")
			centred := a.TermAs[Fun[Real, Real]]("λx:real. (x - m) * (x - m)")
			shifted := a.TermAs[Fun[Real, Real]]("λx:real. x - m")
			scale := a.TermAs[Real]("real_sqrt(v)")
			zero := a.TermAs[Real]("&0")
			root := a.Have(
				"√v squares to v",
				"real_sqrt(v) * real_sqrt(v) = v",
				ByArith(positive, real_sqrt.SqrtPowTwo.At(v)))
			centredMeasurable := a.Have(
				"(x − m)² is continuous, hence Borel",
				"real_measurable(𝕌, borel_sets(real_topology), λx:real. (x - m) * (x - m))",
				By(
					real_continuous.ContinuousOnId.At(line),
					real_continuous.ContinuousOnConst.At(m, line),
					real_continuous.ContinuousOnSub.At(identity, a.TermAs[Fun[Real, Real]]("λx:real. m"), line),
					real_continuous.ContinuousOnMul.At(shifted, shifted, line),
					borel_function.ContinuousBorelMeasurable.At(centred)))
			meanForm := a.Have(
				"under y ↦ m + √v·y the identity is m + √v·y + 0·y²",
				"(λy:real. m + real_sqrt(v) * y) = (λx:real. m + real_sqrt(v) * x + &0 * (x * x))",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[Real]("y")
					b.Show(
						"add the zero term",
						ByArith())
				}))
			squareForm := a.Have(
				"the square is m² + 2m√v·y + v·y²",
				"(λy:real. (m + real_sqrt(v) * y) * (m + real_sqrt(v) * y)) = "+
					"(λx:real. m * m + &2 * m * real_sqrt(v) * x + v * (x * x))",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[Real]("y")
					expanded := b.Have(
						"expand the square",
						"(m + real_sqrt(v) * y) * (m + real_sqrt(v) * y) = "+
							"m * m + &2 * m * real_sqrt(v) * y + real_sqrt(v) * real_sqrt(v) * (y * y)",
						ByArith())
					b.Show(
						"√v squares to v",
						By(expanded, root))
				}))
			centredForm := a.Have(
				"and the centred square is v·y²",
				"(λy:real. (m + real_sqrt(v) * y - m) * (m + real_sqrt(v) * y - m)) = "+
					"(λx:real. &0 + &0 * x + v * (x * x))",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[Real]("y")
					expanded := b.Have(
						"cancel m and expand",
						"(m + real_sqrt(v) * y - m) * (m + real_sqrt(v) * y - m) = "+
							"&0 + &0 * y + real_sqrt(v) * real_sqrt(v) * (y * y)",
						ByArith())
					b.Show(
						"√v squares to v",
						By(expanded, root))
				}))
			mean := a.Have(
				"the mean is m",
				"expectation(𝕌, borel_sets(real_topology), normal_distribution(m, v), λx:real. x) = m",
				ByArith(
					positive,
					meanForm,
					std.powersMeasurable,
					normal_distribution.NormalDistributionAffine.At(m, v, identity),
					At(quadraticMoment, m, scale, zero)))
			secondPower := a.Have(
				"the square is integrable",
				"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(m, v), λx:real. x * x)",
				By(
					positive,
					squareForm,
					std.powersMeasurable,
					normal_distribution.NormalDistributionAffine.At(m, v, square),
					At(quadraticMoment, a.TermAs[Real]("m * m"), a.TermAs[Real]("&2 * m * real_sqrt(v)"), v)))
			spread := a.Have(
				"the centred square has expectation v",
				"expectation(𝕌, "+
					"    borel_sets(real_topology), "+
					"    normal_distribution(m, v), "+
					"    λx:real. (x - m) * (x - m)) = "+
					"v",
				ByArith(
					positive,
					centredForm,
					centredMeasurable,
					normal_distribution.NormalDistributionAffine.At(m, v, centred),
					At(quadraticMoment, zero, zero, v)))
			a.Show(
				"the variance is the expectation of the centred square",
				By(
					Normalized,
					mean,
					spread,
					secondPower,
					probability_space.VarianceDef.At(
						line,
						borel,
						a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("normal_distribution(m, v)"),
						identity)))
		})
	}),
})}

// StandardNormalAbsoluteMoment — under the standard normal |x| is integrable
// with expectation √(2/π). −φ is a primitive of x·φ(x), so on each window
// ⟦−R, R⟧ the integral of |x|·φ(x) is 2(φ(0) − φ(R)); φ(n) is at most
// e^{1/2}·e^{−n}/√(2π) and tends to 0, so the windows tend to
// 2φ(0) = 2/√(2π) = √(2/π).
var StandardNormalAbsoluteMoment = standardNormalAbsoluteMomentThm{family.Add(registry.ProofEntry{
	Name: "StandardNormalAbsoluteMoment",
	Key:  "prop_b09f94ccae5019e7",
	Build: family.Sections(Statement{
		Conclusion: "real_integrable(𝕌, " +
			"    borel_sets(real_topology), " +
			"    normal_distribution(&0, &1), " +
			"    λx:real. |x|) ∧ " +
			"expectation(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λx:real. |x|) = " +
			"real_sqrt(&2 / π)",
		Abbrev: Abbrev{
			{Name: "lebesgueSets", Text: "{E:set(real) | lebesgue_measurable(E)}"},
			{Name: "densityMeasure", Text: "density_measure(𝕌, " +
				"    «lebesgueSets», " +
				"    lebesgue_outer_measure, " +
				"    λx:real. extended_of_real(normal_density(&0, &1, x)))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		std := standardDensitySections(ctx)
		absWindow := ctx.Lemma(Statement{
			Binders: "∀R:real.",
			Hypotheses: []string{
				"&0 ≤ R",
			},
			Conclusion: "real_integral(λy:real. |y| * normal_density(&0, &1, y), -R, R) = " +
				"&2 * normal_density(&0, &1, &0) - &2 * normal_density(&0, &1, R)",
		}, func(a *Argument, R *Expr[Real], radius Fact) {
			zero := a.TermAs[Real]("&0")
			left := a.TermAs[Real]("-R")
			weighted := a.TermAs[Fun[Real, Real]]("λy:real. y * normal_density(&0, &1, y)")
			absolute := a.TermAs[Fun[Real, Real]]("λy:real. |y| * normal_density(&0, &1, y)")
			primitive := a.TermAs[Fun[Real, Real]]("λy:real. -normal_density(&0, &1, y)")
			density := a.TermAs[Fun[Real, Real]]("normal_density(&0, &1)")
			rightHalf := a.TermAs[Set[Real]]("⟦&0, R⟧")
			leftHalf := a.TermAs[Set[Real]]("⟦-R, &0⟧")
			rightValue := a.TermAs[Real]("-normal_density(&0, &1, R) - -normal_density(&0, &1, &0)")
			leftValue := a.TermAs[Real]("-normal_density(&0, &1, &0) - -normal_density(&0, &1, -R)")
			reflected := a.Have(
				"the window's left end is at most 0",
				"-R ≤ &0",
				ByArith(radius))
			rightIncrement := a.Have(
				"on ⟦0, R⟧ the integral of y·φ(y) is the increment of its primitive −φ",
				"real_has_integral(λy:real. y * normal_density(&0, &1, y), "+
					"    &0, "+
					"    R, "+
					"    -normal_density(&0, &1, R) - -normal_density(&0, &1, &0))",
				By(
					radius,
					At(std.continuous, rightHalf),
					real_continuous.ContinuousOnNeg.At(density, rightHalf),
					At(std.weightedContinuous, rightHalf),
					std.negativeDerivative,
					real_integral.NewtonLeibnizContinuous.At(primitive, weighted, zero, R)))
			leftIncrement := a.Have(
				"and on ⟦−R, 0⟧",
				"real_has_integral(λy:real. y * normal_density(&0, &1, y), "+
					"    -R, "+
					"    &0, "+
					"    -normal_density(&0, &1, &0) - -normal_density(&0, &1, -R))",
				By(
					reflected,
					At(std.continuous, leftHalf),
					real_continuous.ContinuousOnNeg.At(density, leftHalf),
					At(std.weightedContinuous, leftHalf),
					std.negativeDerivative,
					real_integral.NewtonLeibnizContinuous.At(primitive, weighted, left, zero)))
			rightAgreement := a.Have(
				"on ⟦0, R⟧ |y| is y",
				"∀x:real. &0 ≤ x ∧ x ≤ R ⇒ x * normal_density(&0, &1, x) = |x| * normal_density(&0, &1, x)",
				Derive(func(b *Argument) {
					b.FixAs[Real]("x")
					inside := b.Assume()
					b.Show(
						"a nonnegative x is its absolute value",
						ByArith(inside))
				}))
			leftAgreement := a.Have(
				"on ⟦−R, 0⟧ |y| is −y",
				"∀x:real. -R ≤ x ∧ x ≤ &0 ⇒ -(x * normal_density(&0, &1, x)) = |x| * normal_density(&0, &1, x)",
				Derive(func(b *Argument) {
					b.FixAs[Real]("x")
					inside := b.Assume()
					b.Show(
						"a nonpositive x is minus its absolute value",
						ByArith(inside))
				}))
			rightAbsolute := a.Have(
				"so on ⟦0, R⟧ the integral of |y|·φ(y) is φ(0) − φ(R)",
				"real_has_integral(λy:real. |y| * normal_density(&0, &1, y), "+
					"    &0, "+
					"    R, "+
					"    -normal_density(&0, &1, R) - -normal_density(&0, &1, &0))",
				By(
					rightIncrement,
					rightAgreement,
					real_integral.HasIntegralCongruence.At(weighted, absolute, zero, R, rightValue)))
			leftAbsolute := a.Have(
				"and on ⟦−R, 0⟧ it is the negated increment φ(0) − φ(−R)",
				"real_has_integral(λy:real. |y| * normal_density(&0, &1, y), "+
					"    -R, "+
					"    &0, "+
					"    -(-normal_density(&0, &1, &0) - -normal_density(&0, &1, -R)))",
				By(
					leftIncrement,
					leftAgreement,
					real_integral.HasIntegralNeg.At(weighted, left, zero, leftValue),
					real_integral.HasIntegralCongruence.At(
						a.TermAs[Fun[Real, Real]]("λx:real. -(x * normal_density(&0, &1, x))"),
						absolute,
						left,
						zero,
						a.TermAs[Real]("-(-normal_density(&0, &1, &0) - -normal_density(&0, &1, -R))"))))
			whole := a.Have(
				"the two halves make up the window",
				"real_has_integral(λy:real. |y| * normal_density(&0, &1, y), "+
					"    -R, "+
					"    R, "+
					"    -(-normal_density(&0, &1, &0) - -normal_density(&0, &1, -R)) + "+
					"    (-normal_density(&0, &1, R) - -normal_density(&0, &1, &0)))",
				By(
					reflected,
					radius,
					leftAbsolute,
					rightAbsolute,
					real_integral.HasIntegralSplit.At(
						absolute,
						left,
						zero,
						R,
						a.TermAs[Real]("-(-normal_density(&0, &1, &0) - -normal_density(&0, &1, -R))"),
						rightValue)))
			a.Show(
				"φ is even, so the two halves are equal",
				ByArith(
					whole,
					At(std.even, R),
					real_integral.HasIntegralValue.At(
						absolute,
						left,
						R,
						a.TermAs[Real]("-(-normal_density(&0, &1, &0) - -normal_density(&0, &1, -R)) + "+
							"(-normal_density(&0, &1, R) - -normal_density(&0, &1, &0))"))))
		})
		densityVanishes := ctx.Lemma("(λn:num. normal_density(&0, &1, &n)) ⟶ &0",
			func(a *Argument) {
				zero := a.TermAs[Real]("&0")
				ratio := a.TermAs[Real]("exp(-&1)")
				scale := a.TermAs[Real]("&1 / real_sqrt(&2 * π) * exp(&1 / &2)")
				contraction := a.Have(
					"e^{−1} lies strictly between 0 and 1",
					"|exp(-&1)| < &1",
					ByArith(
						real_exp_log.ExpPositive.At(a.TermAs[Real]("-&1")),
						real_exp_log.ExpLessIff.At(a.TermAs[Real]("-&1"), zero),
						real_exp_log.ExpZero))
				positiveScale := a.Have(
					"1/√(2π) is positive",
					"&0 < &1 / real_sqrt(&2 * π)",
					ByArith(
						real_trigonometry.PiBounds,
						real_sqrt.SqrtPos.At(a.TermAs[Real]("&2 * π")),
						real_order_field.DivPos.At(a.TermAs[Real]("&1"), a.TermAs[Real]("real_sqrt(&2 * π)"))))
				bound := a.Have(
					"φ(n) is nonnegative and at most e^{1/2}·e^{−n}/√(2π)",
					"∀n:num. "+
						"    &0 ≤ normal_density(&0, &1, &n) ∧ "+
						"    normal_density(&0, &1, &n) ≤ &1 / real_sqrt(&2 * π) * exp(&1 / &2) * exp(-&1) ^ n",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						point := b.TermAs[Real]("&n")
						lower := b.TermAs[Real]("-(&n * &n / &2)")
						upper := b.TermAs[Real]("&n * -&1 + &1 / &2")
						exponent := b.Have(
							"−n²/2 ≤ 1/2 − n, as (n − 1)² ≥ 0",
							"-(&n * &n / &2) ≤ &n * -&1 + &1 / &2",
							ByArith(real_pow.PowTwoNonneg.At(b.TermAs[Real]("&n - &1"))))
						monotone := b.Have(
							"so e^{−n²/2} ≤ e^{1/2}·e^{−n}",
							"exp(-(&n * &n / &2)) ≤ exp(&1 / &2) * exp(-&1) ^ n",
							ByArith(
								exponent,
								real_exp_log.ExpLessIff.At(upper, lower),
								real_exp_log.ExpAdd.At(b.TermAs[Real]("&n * -&1"), b.TermAs[Real]("&1 / &2")),
								real_exp_log.ExpNatMul.At(n, b.TermAs[Real]("-&1"))))
						b.Show(
							"φ(n) is e^{−n²/2}/√(2π)",
							ByArith(
								monotone,
								positiveScale,
								At(std.formula, point),
								At(std.nonnegative, point),
								real_order_ring.LessEqMulLeft.At(
									b.TermAs[Real]("&1 / real_sqrt(&2 * π)"),
									b.TermAs[Real]("exp(-(&n * &n / &2))"),
									b.TermAs[Real]("exp(&1 / &2) * exp(-&1) ^ n"))))
					}))
				powers := a.Have(
					"e^{1/2}·e^{−n}/√(2π) tends to 0",
					"(λn:num. &1 / real_sqrt(&2 * π) * exp(&1 / &2) * exp(-&1) ^ n) ⟶ &0",
					By(
						contraction,
						real_sequences.PowerTendsToZero.At(ratio),
						real_sequences.LimitScale.At(a.TermAs[Fun[Nat, Real]]("λn:num. exp(-&1) ^ n"), zero, scale),
						real_ring.MulRightZero.At(scale)))
				a.Show(
					"φ(n) is squeezed between 0 and a vanishing sequence",
					By(
						bound,
						powers,
						real_sequences.LimitConst.At(zero),
						real_sequences.LimitSqueeze.At(
							a.TermAs[Fun[Nat, Real]]("λn:num. &0"),
							a.TermAs[Fun[Nat, Real]]("λn:num. normal_density(&0, &1, &n)"),
							a.TermAs[Fun[Nat, Real]]("λn:num. &1 / real_sqrt(&2 * π) * exp(&1 / &2) * exp(-&1) ^ n"),
							zero,
							a.TermAs[Nat]("0"))))
			})
		absWindows := ctx.Lemma("(λn:num. "+
			"    real_integral(λy:real. |y| * normal_density(&0, &1, y), -&n, &n)) ⟶ "+
			"&2 * normal_density(&0, &1, &0)",
			func(a *Argument) {
				centre := a.TermAs[Real]("&2 * normal_density(&0, &1, &0)")
				windows := a.Have(
					"each window of |y|·φ(y) is 2φ(0) − 2φ(n)",
					"(λn:num. real_integral(λy:real. |y| * normal_density(&0, &1, y), -&n, &n)) = "+
						"(λn:num. &2 * normal_density(&0, &1, &0) - &2 * normal_density(&0, &1, &n))",
					Funext(),
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.Show(
							"the window identity at radius n",
							By(real_order_ring.NumNonneg.At(n), At(absWindow, b.TermAs[Real]("&n"))))
					}))
				a.Show(
					"φ(n) tends to 0",
					By(
						windows,
						densityVanishes,
						real_ring.MulRightZero.At(a.TermAs[Real]("&2")),
						real_ring.SubRightZero.At(centre),
						real_sequences.LimitConst.At(centre),
						real_sequences.LimitScale.At(
							a.TermAs[Fun[Nat, Real]]("λn:num. normal_density(&0, &1, &n)"),
							a.TermAs[Real]("&0"),
							a.TermAs[Real]("&2")),
						real_sequences.LimitSub.At(
							a.TermAs[Fun[Nat, Real]]("λn:num. &2 * normal_density(&0, &1, &0)"),
							a.TermAs[Fun[Nat, Real]]("λn:num. &2 * normal_density(&0, &1, &n)"),
							centre,
							a.TermAs[Real]("&2 * &0"))))
			})
		return ctx.Theorem(headline, func(a *Argument) {
			line := a.TermAs[Set[Real]]("𝕌")
			borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
			identity := a.TermAs[Fun[Real, Real]]("λx:real. x")
			density := a.TermAs[Fun[Real, Real]]("normal_density(&0, &1)")
			absolute := a.TermAs[Fun[Real, Real]]("λy:real. |y| * normal_density(&0, &1, y)")
			nonnegative := a.Have(
				"|y|·φ(y) is nonnegative",
				"∀x:real. &0 ≤ |x| * normal_density(&0, &1, x)",
				Derive(func(b *Argument) {
					x := b.FixAs[Real]("x")
					b.Show(
						"an absolute value times a nonnegative density",
						ByArith(At(std.nonnegative, x)))
				}))
			continuous := a.Have(
				"|y|·φ(y) is continuous on the line",
				"real_continuous_on(𝕌, λy:real. |y| * normal_density(&0, &1, y))",
				By(
					real_continuous.ContinuousOnId.At(line),
					real_continuous.ContinuousOnAbs.At(identity, line),
					At(std.continuous, line),
					real_continuous.ContinuousOnMul.At(a.TermAs[Fun[Real, Real]]("λx:real. |x|"), density, line)))
			lebesgue := a.Have(
				"its windows tend to 2φ(0), so |y|·φ(y) is Lebesgue integrable with integral 2φ(0)",
				"real_integrable(𝕌, "+
					"    «lebesgueSets», "+
					"    lebesgue_outer_measure, "+
					"    λy:real. |y| * normal_density(&0, &1, y)) ∧ "+
					"measure_integral(𝕌, "+
					"    «lebesgueSets», "+
					"    lebesgue_outer_measure, "+
					"    λy:real. |y| * normal_density(&0, &1, y)) = "+
					"&2 * normal_density(&0, &1, &0)",
				By(
					nonnegative,
					continuous,
					absWindows,
					lebesgue_riemann.LebesgueIntegralByCenteredWindows.At(
						absolute,
						a.TermAs[Real]("&2 * normal_density(&0, &1, &0)"))))
			integrand := a.Have(
				"φ times |x| is |y|·φ(y)",
				"(λy:real. |y| * normal_density(&0, &1, y)) = (λx:real. normal_density(&0, &1, x) * |x|)",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[Real]("y")
					b.Show(
						"commute the product",
						ByArith())
				}))
			absBorel := a.Have(
				"|x| is Borel",
				"real_measurable(𝕌, borel_sets(real_topology), λx:real. |x|)",
				By(
					std.powersMeasurable,
					borel_function.LineBorelSigmaAlgebra,
					measurable_function.RealMeasurableAbs.At(line, borel, identity)))
			unitPeak := a.Have(
				"e^{−0²/2} is 1",
				"exp(-(&0 * &0 / &2)) = &1",
				Simp(
					Fwd(real_ring.MulRightZero),
					Fwd(real_field.RealDivDef),
					Fwd(real_ring.MulLeftZero),
					Fwd(real_ring.NegZero),
					Fwd(real_exp_log.ExpZero)),
				Refl())
			centre := a.Have(
				"φ(0) is 1/√(2π)",
				"normal_density(&0, &1, &0) = &1 / real_sqrt(&2 * π)",
				ByArith(At(std.formula, a.TermAs[Real]("&0")), unitPeak))
			value := a.Have(
				"2/√(2π) is √(2/π)",
				"&2 * (&1 / real_sqrt(&2 * π)) = real_sqrt(&2 / π)",
				ByArith(
					real_trigonometry.PiBounds,
					real_sqrt.SqrtPowTwo.At(a.TermAs[Real]("&2 * π")),
					real_sqrt.SqrtPos.At(a.TermAs[Real]("&2 * π")),
					real_sqrt.SqrtUnique.At(a.TermAs[Real]("&2 / π"), a.TermAs[Real]("&2 * (&1 / real_sqrt(&2 * π))"))))
			a.Show(
				"|x| is Borel, so its expectation is that Lebesgue integral",
				By(
					integrand,
					lebesgue,
					centre,
					value,
					absBorel,
					At(std.transport, a.TermAs[Fun[Real, Real]]("λx:real. |x|"))))
		})
	}),
})}

// StandardNormalThirdAbsoluteMomentValue — under the standard normal |x|³ is
// integrable with expectation 2√(2/π). With φ the standard density,
// (y² + 2)·φ(y) has derivative −y³·φ(y), so it is a primitive of |y|³·φ(y)
// on ⟦−R, 0⟧ and its negative one on ⟦0, R⟧: each half of the window
// ⟦−R, R⟧ integrates to 2φ(0) − (R² + 2)·φ(R). The boundary term tends to 0,
// x·(x² + 2)·e^{−x²/2} being bounded, so the windows tend to 4φ(0), which is
// 2√(2/π).
var StandardNormalThirdAbsoluteMomentValue = standardNormalThirdAbsoluteMomentValueThm{family.Add(registry.ProofEntry{
	Name: "StandardNormalThirdAbsoluteMomentValue",
	Key:  "prop_b3d9f4e0ac24de9b",
	Build: family.Sections(Statement{
		Conclusion: "real_integrable(𝕌, " +
			"    borel_sets(real_topology), " +
			"    normal_distribution(&0, &1), " +
			"    λx:real. |x| * x * x) ∧ " +
			"expectation(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λx:real. |x| * x * x) = " +
			"&2 * real_sqrt(&2 / π)",
		Abbrev: Abbrev{
			{Name: "lebesgueSets", Text: "{E:set(real) | lebesgue_measurable(E)}"},
			{Name: "densityMeasure", Text: "density_measure(𝕌, " +
				"    «lebesgueSets», " +
				"    lebesgue_outer_measure, " +
				"    λx:real. extended_of_real(normal_density(&0, &1, x)))"},
			{Name: "weightedCube", Text: "λx:real. |x| * x * x * normal_density(&0, &1, x)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		std := standardDensitySections(ctx)
		primitive := ctx.Lemma("∀x:real. "+
			"    real_derivative_at(λy:real. (y * y + &2) * normal_density(&0, &1, y), "+
			"        x, "+
			"        -(x * x * x * normal_density(&0, &1, x)))",
			func(a *Argument, x *Expr[Real]) {
				identity := a.TermAs[Fun[Real, Real]]("λy:real. y")
				one := a.TermAs[Real]("&1")
				shifted := a.Have(
					"y² + 2 has derivative 2x at x",
					"real_derivative_at(λy:real. y * y + &2, x, &2 * x)",
					ByArith(
						real_derivative.DerivativeId.At(x),
						real_derivative.DerivativeMul.At(identity, identity, x, one, one),
						real_derivative.DerivativeConst.At(a.TermAs[Real]("&2"), x),
						real_derivative.DerivativeAdd.At(
							a.TermAs[Fun[Real, Real]]("λy:real. y * y"),
							a.TermAs[Fun[Real, Real]]("λy:real. &2"),
							x,
							a.TermAs[Real]("&2 * x"),
							a.TermAs[Real]("&0"))))
				a.Show(
					"by the product rule and φ′(x) = −x·φ(x), the derivative is 2x·φ(x) − (x² + 2)·x·φ(x) = −x³·φ(x)",
					ByArith(
						shifted,
						At(std.derivative, x),
						real_derivative.DerivativeMul.At(
							a.TermAs[Fun[Real, Real]]("λy:real. y * y + &2"),
							a.TermAs[Fun[Real, Real]]("normal_density(&0, &1)"),
							x,
							a.TermAs[Real]("&2 * x"),
							a.TermAs[Real]("-x * normal_density(&0, &1, x)"))))
			})
		continuous := ctx.Lemma("∀S:set(real). real_continuous_on(S, «weightedCube»)",
			func(a *Argument, S *Expr[Set[Real]]) {
				identity := a.TermAs[Fun[Real, Real]]("λx:real. x")
				a.Show(
					"|x|, x and φ are continuous, and so are their products",
					By(
						real_continuous.ContinuousOnId.At(S),
						real_continuous.ContinuousOnAbs.At(identity, S),
						At(std.continuous, S),
						real_continuous.ContinuousOnMul.At(a.TermAs[Fun[Real, Real]]("λx:real. |x|"), identity, S),
						real_continuous.ContinuousOnMul.At(a.TermAs[Fun[Real, Real]]("λx:real. |x| * x"), identity, S),
						real_continuous.ContinuousOnMul.At(
							a.TermAs[Fun[Real, Real]]("λx:real. |x| * x * x"),
							a.TermAs[Fun[Real, Real]]("normal_density(&0, &1)"),
							S)))
			})
		windowIdentity := ctx.Lemma(Statement{
			Binders: "∀R:real.",
			Hypotheses: []string{
				"&0 ≤ R",
			},
			Conclusion: "real_integral(«weightedCube», -R, R) = " +
				"&4 * normal_density(&0, &1, &0) - &2 * ((R * R + &2) * normal_density(&0, &1, R))",
		}, func(a *Argument, R *Expr[Real], radius Fact) {
			zero := a.TermAs[Real]("&0")
			left := a.TermAs[Real]("-R")
			weighted := a.TermAs[Fun[Real, Real]]("«weightedCube»")
			lift := a.TermAs[Fun[Real, Real]]("λy:real. (y * y + &2) * normal_density(&0, &1, y)")
			slope := a.TermAs[Fun[Real, Real]]("λx:real. -(x * x * x * normal_density(&0, &1, x))")
			upperHalf := a.TermAs[Set[Real]]("⟦&0, R⟧")
			lowerHalf := a.TermAs[Set[Real]]("⟦-R, &0⟧")
			order := a.Have(
				"the window and its halves are ordered",
				"-R ≤ &0 ∧ -R ≤ R",
				ByArith(radius))
			rising := a.Have(
				"inside ⟦0, R⟧, |x| = x, so −(y² + 2)·φ(y) has derivative |x|·x²·φ(x)",
				Statement{
					Binders:    "∀x:real.",
					Hypotheses: []string{"&0 < x", "x < R"},
					Conclusion: "real_derivative_at(λy:real. -((y * y + &2) * normal_density(&0, &1, y)), " +
						"    x, " +
						"    |x| * x * x * normal_density(&0, &1, x))",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[Real]("x")
					inside := b.Assume()
					b.Show(
						"negate the derivative of (y² + 2)·φ(y)",
						ByArith(
							inside,
							At(primitive, x),
							real_derivative.DerivativeNeg.At(
								lift, x, b.TermAs[Real]("-(x * x * x * normal_density(&0, &1, x))"))))
				}))
			falling := a.Have(
				"inside ⟦−R, 0⟧, |x| = −x, so (y² + 2)·φ(y) has derivative |x|·x²·φ(x)",
				Statement{
					Binders:    "∀x:real.",
					Hypotheses: []string{"-R < x", "x < &0"},
					Conclusion: "real_derivative_at(λy:real. (y * y + &2) * normal_density(&0, &1, y), " +
						"    x, " +
						"    |x| * x * x * normal_density(&0, &1, x))",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[Real]("x")
					inside := b.Assume()
					b.Show(
						"−x³·φ(x) is |x|·x²·φ(x) for negative x",
						ByArith(inside, At(primitive, x)))
				}))
			liftContinuous := a.Have(
				"(y² + 2)·φ(y) has a derivative everywhere, so it is continuous on both halves",
				"real_continuous_on(⟦&0, R⟧, λy:real. (y * y + &2) * normal_density(&0, &1, y)) ∧ "+
					"real_continuous_on(⟦-R, &0⟧, λy:real. (y * y + &2) * normal_density(&0, &1, y))",
				By(
					primitive,
					real_derivative.DerivativeContinuousOn.At(lift, slope, upperHalf),
					real_derivative.DerivativeContinuousOn.At(lift, slope, lowerHalf)))
			upper := a.Have(
				"so the upper half integrates to 2φ(0) − (R² + 2)·φ(R)",
				"real_integral(«weightedCube», &0, R) = "+
					"&2 * normal_density(&0, &1, &0) - (R * R + &2) * normal_density(&0, &1, R)",
				ByArith(
					radius,
					rising,
					liftContinuous,
					At(continuous, upperHalf),
					real_continuous.ContinuousOnNeg.At(lift, upperHalf),
					real_integral.NewtonLeibnizContinuous.At(
						a.TermAs[Fun[Real, Real]]("λy:real. -((y * y + &2) * normal_density(&0, &1, y))"),
						weighted,
						zero,
						R),
					At(real_integral.HasIntegralValue, weighted, zero, R)))
			lower := a.Have(
				"and the lower half, φ being even, to the same",
				"real_integral(«weightedCube», -R, &0) = "+
					"&2 * normal_density(&0, &1, &0) - (R * R + &2) * normal_density(&0, &1, R)",
				ByArith(
					order,
					falling,
					liftContinuous,
					At(continuous, lowerHalf),
					At(std.even, R),
					real_integral.NewtonLeibnizContinuous.At(lift, weighted, left, zero),
					At(real_integral.HasIntegralValue, weighted, left, zero)))
			a.Show(
				"the window is the sum of its halves",
				ByArith(
					radius,
					order,
					upper,
					lower,
					At(continuous, a.TermAs[Set[Real]]("⟦-R, R⟧")),
					real_integral.IntegralAdditive.At(weighted, left, R, left, zero, R)))
		})
		boundaryBound := ctx.Lemma(Statement{
			Binders: "∀x:real.",
			Hypotheses: []string{
				"&0 ≤ x",
			},
			Conclusion: "x * ((x * x + &2) * normal_density(&0, &1, x)) ≤ &15 * (&1 / real_sqrt(&2 * π))",
		}, func(a *Argument, x *Expr[Real], nonnegative Fact) {
			decay := a.TermAs[Real]("-(x * x / &4)")
			bound := a.TermAs[Real]("&1 / real_sqrt(&2 * π)")
			kernel := a.Have(
				"t·e^{−t} ≤ 1 at t = x²/4, and e^{−x²/2} is the square of e^{−x²/4}, which lies in ⟦0, 1⟧",
				"x * x * exp(-(x * x / &4)) ≤ &4 ∧ "+
					"&0 < exp(-(x * x / &4)) ∧ "+
					"exp(-(x * x / &4)) ≤ &1 ∧ "+
					"exp(-(x * x / &2)) = exp(-(x * x / &4)) * exp(-(x * x / &4))",
				ByArith(
					nonnegative,
					real_exp_log.ExpNegMulBound.At(a.TermAs[Real]("x * x / &4")),
					real_exp_log.ExpAdd.At(decay, decay),
					real_exp_log.ExpPositive.At(decay),
					real_exp_log.ExpLessIff.At(a.TermAs[Real]("&0"), decay),
					real_exp_log.ExpZero))
			weightedSquare := a.Have(
				"e^{−x²/4}·(x − 1)² is nonnegative",
				"&0 ≤ exp(-(x * x / &4)) * ((x - &1) * (x - &1))",
				ByArith(kernel))
			linear := a.Have(
				"so 2x·e^{−x²/4} ≤ x²·e^{−x²/4} + e^{−x²/4} ≤ 5",
				"&0 ≤ x * x * exp(-(x * x / &4)) ∧ "+
					"&0 ≤ x * exp(-(x * x / &4)) ∧ "+
					"&2 * (x * exp(-(x * x / &4))) ≤ &5",
				ByArith(nonnegative, kernel, weightedSquare))
			cubic := a.Have(
				"x·(x² + 2)·e^{−x²/2} is x²e^{−x²/4}·xe^{−x²/4} + 2·xe^{−x²/4}·e^{−x²/4}, at most 4·5/2 + 5",
				"x * ((x * x + &2) * exp(-(x * x / &2))) ≤ &15",
				ByArith(DenotedAs("e", a.TermAs[Real]("exp(-(x * x / &4))")), nonnegative, kernel, linear))
			positive := a.Have(
				"1/√(2π) is positive",
				"&0 ≤ &1 / real_sqrt(&2 * π)",
				ByArith(
					real_trigonometry.PiBounds,
					real_sqrt.SqrtPos.At(a.TermAs[Real]("&2 * π")),
					real_order_field.DivPos.At(a.TermAs[Real]("&1"), a.TermAs[Real]("real_sqrt(&2 * π)"))))
			a.Show(
				"φ(x) is e^{−x²/2}/√(2π)",
				Simp(Fwd(std.formula)),
				ByArith(
					cubic,
					positive,
					real_order_ring.LessEqMulLeft.At(
						bound, a.TermAs[Real]("x * ((x * x + &2) * exp(-(x * x / &2)))"), a.TermAs[Real]("&15"))))
		})
		boundaryVanishes := ctx.Lemma("(λn:num. (&n * &n + &2) * normal_density(&0, &1, &n)) ⟶ &0",
			func(a *Argument) {
				bound := a.TermAs[Real]("&15 * (&1 / real_sqrt(&2 * π))")
				a.Show(
					"for ε > 0, past an N with 15/√(2π) < N·ε the term is below ε",
					Simp(Fwd(real_sequences.RealConvergesToDef)),
					Derive(func(b *Argument) {
						ε := b.FixAs[Real]("ε")
						positive := b.Assume()
						N, large := b.ObtainAs[Nat](
							"N exists by the Archimedean property",
							"∃N:num. &15 * (&1 / real_sqrt(&2 * π)) < &N * ε",
							By(positive, real_archimedean.Archimedean.At(ε, bound)))
						b.Show(
							"this N serves",
							Witness(N),
							Derive(func(c *Argument) {
								n := c.FixAs[Nat]("n")
								past := c.Assume()
								index := c.TermAs[Real]("&n")
								nonnegative := c.Have(
									"n is nonnegative",
									"&0 ≤ &n",
									By(real_order_ring.NumNonneg.At(n)))
								grows := c.Have(
									"ε·N ≤ ε·n",
									"ε * &N ≤ ε * &n",
									ByArith(
										past,
										positive,
										real_construction.OfNumLessEq.At(N, n),
										real_order_ring.LessEqMulLeft.At(ε, c.TermAs[Real]("&N"), index)))
								boundary := c.Have(
									"n·(n² + 2)·φ(n) ≤ 15/√(2π) < N·ε ≤ n·ε",
									"&n * ((&n * &n + &2) * normal_density(&0, &1, &n)) < &n * ε",
									ByArith(grows, large, nonnegative, At(boundaryBound, index)))
								termNonnegative := c.Have(
									"the term is nonnegative, so its distance from 0 is itself",
									"|(&n * &n + &2) * normal_density(&0, &1, &n) - &0| = (&n * &n + &2) * normal_density(&0, &1, &n)",
									ByArith(
										At(std.nonnegative, index),
										real_sgn_abs.AbsFixedIffNonneg.At(c.TermAs[Real]("(&n * &n + &2) * normal_density(&0, &1, &n)"))))
								c.Cases(c.TermAs[Bool]("&n = &0"))
								c.When(
									"at n = 0 the threshold N would be 0, against 15/√(2π) < N·ε",
									func(d *Argument, zero Fact) {
										d.Show(
											"no such n is past N",
											ByArith(zero, grows, large, nonnegative, At(boundaryBound, index)))
									})
								c.Otherwise(
									"otherwise n is positive and cancels from both sides",
									func(d *Argument, nonzero Fact) {
										positiveIndex := d.Have(
											"n is positive",
											"&0 < &n",
											ByArith(nonzero, nonnegative))
										d.Show(
											"so the term is below ε",
											ByArith(positiveIndex, boundary, termNonnegative))
									})
							}))
					}))
			})
		windowLimit := ctx.Lemma("(λn:num. real_integral(«weightedCube», -&n, &n)) ⟶ "+
			"&4 * normal_density(&0, &1, &0)",
			func(a *Argument) {
				centre := a.TermAs[Real]("&4 * normal_density(&0, &1, &0)")
				boundary := a.TermAs[Fun[Nat, Real]]("λn:num. (&n * &n + &2) * normal_density(&0, &1, &n)")
				windows := a.Have(
					"each window is 4φ(0) less twice the boundary term",
					"(λn:num. real_integral(«weightedCube», -&n, &n)) = "+
						"(λn:num. &4 * normal_density(&0, &1, &0) - &2 * ((&n * &n + &2) * normal_density(&0, &1, &n)))",
					Funext(),
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.Show(
							"the window identity at radius n",
							By(real_order_ring.NumNonneg.At(n), At(windowIdentity, b.TermAs[Real]("&n"))))
					}))
				a.Show(
					"the boundary term tends to 0",
					ByArith(
						windows,
						boundaryVanishes,
						real_sequences.LimitConst.At(centre),
						real_sequences.LimitScale.At(boundary, a.TermAs[Real]("&0"), a.TermAs[Real]("&2")),
						real_sequences.LimitSub.At(
							a.TermAs[Fun[Nat, Real]]("λn:num. &4 * normal_density(&0, &1, &0)"),
							a.TermAs[Fun[Nat, Real]]("λn:num. &2 * ((&n * &n + &2) * normal_density(&0, &1, &n))"),
							centre,
							a.TermAs[Real]("&2 * &0"))))
			})
		peak := ctx.Lemma("&4 * normal_density(&0, &1, &0) = &2 * real_sqrt(&2 / π)",
			func(a *Argument) {
				zero := a.TermAs[Real]("&0")
				circle := a.TermAs[Real]("&2 * π")
				ratio := a.TermAs[Real]("&2 / π")
				product := a.Have(
					"(2/π)·(2π) = 4",
					"&2 / π * (&2 * π) = &4",
					ByArith(real_trigonometry.PiBounds))
				roots := a.Have(
					"so √(2/π)·√(2π) = √4 = 2, and √(2π) is positive",
					"real_sqrt(&2 / π) * real_sqrt(&2 * π) = &2 ∧ &0 < real_sqrt(&2 * π)",
					ByArith(
						product,
						real_trigonometry.PiBounds,
						real_sqrt.SqrtMul.At(ratio, circle),
						real_sqrt.SqrtUnique.At(a.TermAs[Real]("&4"), a.TermAs[Real]("&2")),
						real_sqrt.SqrtPos.At(circle)))
				exponent := a.Have(
					"the exponent of φ vanishes at 0",
					"-(&0 * &0 / &2) = &0",
					ByArith())
				atZero := a.Have(
					"so φ(0) = 1/√(2π)",
					"normal_density(&0, &1, &0) * real_sqrt(&2 * π) = &1",
					ByArith(
						roots,
						exponent,
						At(std.formula, zero),
						real_exp_log.ExpZero,
						real_order_field.EqDivMulLeft.At(
							a.TermAs[Real]("normal_density(&0, &1, &0)"),
							a.TermAs[Real]("&1"),
							a.TermAs[Real]("real_sqrt(&2 * π)"))))
				a.Show(
					"and 4φ(0) = 4/√(2π) = 2√(2/π)",
					ByArith(roots, atZero))
			})
		return ctx.Theorem(headline, func(a *Argument) {
			line := a.TermAs[Set[Real]]("𝕌")
			borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
			identity := a.TermAs[Fun[Real, Real]]("λx:real. x")
			absolute := a.TermAs[Fun[Real, Real]]("λx:real. |x|")
			nonnegative := a.Have(
				"|x|·x²·φ(x) is nonnegative",
				"∀x:real. &0 ≤ |x| * x * x * normal_density(&0, &1, x)",
				Derive(func(b *Argument) {
					x := b.FixAs[Real]("x")
					b.Show(
						"a product of nonnegative factors",
						ByArith(real_sgn_abs.AbsNonneg.At(x), At(std.nonnegative, x)))
				}))
			lebesgue := a.Have(
				"its windows tend to 4φ(0), so |x|·x²·φ(x) is Lebesgue integrable with integral 4φ(0)",
				"real_integrable(𝕌, «lebesgueSets», lebesgue_outer_measure, «weightedCube») ∧ "+
					"measure_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, «weightedCube») = "+
					"&4 * normal_density(&0, &1, &0)",
				By(
					nonnegative,
					At(continuous, line),
					windowLimit,
					lebesgue_riemann.LebesgueIntegralByCenteredWindows.At(
						a.TermAs[Fun[Real, Real]]("«weightedCube»"), a.TermAs[Real]("&4 * normal_density(&0, &1, &0)"))))
			cubicMeasurable := a.Have(
				"|x|·x² is Borel, a product of |x| and x twice",
				"real_measurable(𝕌, borel_sets(real_topology), λx:real. |x| * x * x)",
				By(
					std.powersMeasurable,
					borel_function.LineBorelSigmaAlgebra,
					measurable_function.RealMeasurableAbs.At(line, borel, identity),
					measurable_function.RealMeasurableMul.At(line, borel, absolute, identity),
					measurable_function.RealMeasurableMul.At(
						line, borel, a.TermAs[Fun[Real, Real]]("λx:real. |x| * x"), identity)))
			integrand := a.Have(
				"φ times |x|·x² is |x|·x²·φ(x)",
				"«weightedCube» = (λx:real. normal_density(&0, &1, x) * (|x| * x * x))",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[Real]("x")
					b.Show(
						"commute the product",
						ByArith())
				}))
			a.Show(
				"|x|·x² is Borel, so its expectation is that Lebesgue integral, 4φ(0) = 2√(2/π)",
				By(
					integrand,
					lebesgue,
					cubicMeasurable,
					peak,
					At(std.transport, a.TermAs[Fun[Real, Real]]("λx:real. |x| * x * x"))))
		})
	}),
})}

// StandardNormalThirdAbsoluteMoment — under the standard normal |x|³ is
// integrable with expectation at most 2: the expectation is 2√(2/π), and
// π ≥ 2, since cos 1 ≥ 1 − 1/2 is positive while the cosine falls on ⟦0, 2⟧
// to its zero π/2.
var StandardNormalThirdAbsoluteMoment = standardNormalThirdAbsoluteMomentThm{family.Add(registry.ProofEntry{
	Name: "StandardNormalThirdAbsoluteMoment",
	Key:  "prop_8a91cd92d0c3169",
	Build: family.Theorem(Statement{
		Conclusion: "real_integrable(𝕌, " +
			"    borel_sets(real_topology), " +
			"    normal_distribution(&0, &1), " +
			"    λx:real. |x| * x * x) ∧ " +
			"expectation(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λx:real. |x| * x * x) ≤ &2",
	}, func(a *Argument) {
		ratio := a.TermAs[Real]("&2 / π")
		halfTurn := a.Have(
			"π ≥ 2: cos 1 ≥ 1 − 1/2 > 0, while the cosine falls on ⟦0, 2⟧ to cos(π/2) = 0",
			"&2 ≤ π",
			ByArith(
				real_trigonometry.CosTaylorBounds.At(a.TermAs[Real]("&1")),
				real_trigonometry.CosStrictlyDecreasing.At(a.TermAs[Real]("π / &2"), a.TermAs[Real]("&1")),
				real_trigonometry.PiHalfZero))
		unit := a.Have(
			"so 2/π lies in ⟦0, 1⟧",
			"&0 ≤ &2 / π ∧ &2 / π ≤ &1",
			ByArith(halfTurn))
		root := a.Have(
			"so its square root is at most 1",
			"real_sqrt(&2 / π) ≤ &1",
			ByArith(unit, real_sqrt.SqrtPowTwo.At(ratio), real_sqrt.SqrtNonneg.At(ratio)))
		a.Show(
			"the expectation 2√(2/π) is at most 2",
			ByArith(StandardNormalThirdAbsoluteMomentValue, root))
	}),
})}

// standardDensity holds the sections on the standard normal density φ that
// both moment members read.
type standardDensity struct {
	formula, derivative, continuous, even, nonnegative, weightedContinuous, negativeDerivative *GoalStackNode
	windows, powersMeasurable, transport                                                       *GoalStackNode
}

// standardDensitySections proves them: φ(x) = e^{−x²/2}/√(2π) has derivative
// −x·φ(x), so −φ has derivative x·φ(x); φ is continuous, even and
// nonnegative, and so are its products with x and x² continuous. For a
// nonnegative f continuous on the line the windows ⟦−n, n⟧ have nonnegative,
// increasing integrals whose supremum is the integral of f over the line; the
// identity and the square are Borel; and a Borel test integrates against
// normal_distribution(0, 1) as its product with φ against Lebesgue measure.
func standardDensitySections(ctx *Script) standardDensity {
	var std standardDensity
	std.formula = ctx.Lemma("∀x:real. "+
		"    normal_density(&0, &1, x) = &1 / real_sqrt(&2 * π) * exp(-(x * x / &2))",
		func(a *Argument, x *Expr[Real]) {
			a.Show(
				"the density formula at mean 0 and variance 1",
				Simp(
					Fwd(normal_distribution.NormalDensityDef),
					Fwd(real_ring.SubRightZero),
					Fwd(real_ring.MulRightId),
					Fwd(real_pow.PowTwo),
					Fwd(real_field.RealDivDef),
					Fwd(real_construction.MulLeftId)),
				ByArith())
		})
	std.derivative = ctx.Lemma("∀x:real. "+
		"    real_derivative_at(normal_density(&0, &1), x, -x * normal_density(&0, &1, x))",
		func(a *Argument, x *Expr[Real]) {
			identity := a.TermAs[Fun[Real, Real]]("λy:real. y")
			square := a.TermAs[Fun[Real, Real]]("λy:real. y * y")
			exponent := a.TermAs[Fun[Real, Real]]("λy:real. -&1 / &2 * (y * y)")
			one := a.TermAs[Real]("&1")
			form := a.Have(
				"the standard density is 1/√(2π) times the exponential of −y²/2",
				"normal_density(&0, &1) = λy:real. &1 / real_sqrt(&2 * π) * exp(-&1 / &2 * (y * y))",
				Funext(),
				Derive(func(b *Argument) {
					y := b.FixAs[Real]("y")
					half := b.Have(
						"the exponent is −1/2 times the square",
						"-(y * y / &2) = -&1 / &2 * (y * y)",
						ByArith())
					b.Show(
						"the density formula, its exponent regrouped",
						By(At(std.formula, y), half))
				}))
			squareSlope := a.Have(
				"y² has derivative 2x at x, by the product rule",
				"real_derivative_at(λy:real. y * y, x, &2 * x)",
				ByArith(
					real_derivative.DerivativeId.At(x),
					real_derivative.DerivativeMul.At(identity, identity, x, one, one)))
			exponentSlope := a.Have(
				"so −y²/2 has derivative −x",
				"real_derivative_at(λy:real. -&1 / &2 * (y * y), x, -x)",
				ByArith(
					squareSlope,
					real_derivative.DerivativeScale.At(
						square, x, a.TermAs[Real]("&2 * x"), a.TermAs[Real]("-&1 / &2"))))
			chain := a.Have(
				"and its exponential has derivative exp(−x²/2)·(−x), by the chain rule",
				"real_derivative_at(λy:real. exp(-&1 / &2 * (y * y)), x, exp(-&1 / &2 * (x * x)) * -x)",
				By(
					exponentSlope,
					real_exp_log.ExpDerivative.At(a.TermAs[Real]("-&1 / &2 * (x * x)")),
					real_derivative.DerivativeChain.At(
						a.TermAs[Fun[Real, Real]]("real_exp"),
						exponent,
						x,
						a.TermAs[Real]("exp(-&1 / &2 * (x * x))"),
						a.TermAs[Real]("-x")),
					functions.ComposeApply.At(a.TermAs[Fun[Real, Real]]("real_exp"), exponent)))
			regroup := a.Have(
				"the constant factor passes to the front",
				"&1 / real_sqrt(&2 * π) * (exp(-&1 / &2 * (x * x)) * -x) = "+
					"-x * (&1 / real_sqrt(&2 * π) * exp(-&1 / &2 * (x * x)))",
				ByArith())
			a.Show(
				"scaling by 1/√(2π) gives the derivative of the density",
				By(
					form,
					regroup,
					chain,
					real_derivative.DerivativeScale.At(
						a.TermAs[Fun[Real, Real]]("λy:real. exp(-&1 / &2 * (y * y))"),
						x,
						a.TermAs[Real]("exp(-&1 / &2 * (x * x)) * -x"),
						a.TermAs[Real]("&1 / real_sqrt(&2 * π)"))))
		})
	std.continuous = ctx.Lemma("∀S:set(real). real_continuous_on(S, normal_density(&0, &1))",
		func(a *Argument, S *Expr[Set[Real]]) {
			a.Show(
				"a function with a derivative everywhere is continuous",
				By(
					std.derivative,
					real_derivative.DerivativeContinuousOn.At(
						a.TermAs[Fun[Real, Real]]("normal_density(&0, &1)"),
						a.TermAs[Fun[Real, Real]]("λx:real. -x * normal_density(&0, &1, x)"),
						S)))
		})
	std.even = ctx.Lemma("∀x:real. normal_density(&0, &1, -x) = normal_density(&0, &1, x)",
		func(a *Argument, x *Expr[Real]) {
			zero, one := a.TermAs[Real]("&0"), a.TermAs[Real]("&1")
			reflected := a.Have(
				"reflection keeps the square in the exponent",
				"(-x - &0) ^ 2 = (x - &0) ^ 2",
				ByArith(
					real_pow.PowTwo.At(a.TermAs[Real]("-x - &0")),
					real_pow.PowTwo.At(a.TermAs[Real]("x - &0"))))
			a.Show(
				"so the density takes one value at x and −x",
				By(
					reflected,
					normal_distribution.NormalDensityDef.At(zero, one, a.TermAs[Real]("-x")),
					normal_distribution.NormalDensityDef.At(zero, one, x)))
		})
	std.nonnegative = ctx.Lemma("∀x:real. &0 ≤ normal_density(&0, &1, x)",
		func(a *Argument, x *Expr[Real]) {
			a.Show(
				"an exponential over a positive root",
				ByArith(
					real_trigonometry.PiBounds,
					real_sqrt.SqrtPos.At(a.TermAs[Real]("&2 * π * &1")),
					real_exp_log.ExpPositive.At(a.TermAs[Real]("-((x - &0) ^ 2 / (&2 * &1))")),
					normal_distribution.NormalDensityDef.At(a.TermAs[Real]("&0"), a.TermAs[Real]("&1"), x)))
		})
	std.weightedContinuous = ctx.Lemma("∀S:set(real). "+
		"    real_continuous_on(S, λx:real. x * normal_density(&0, &1, x)) ∧ "+
		"    real_continuous_on(S, λx:real. x * x * normal_density(&0, &1, x))",
		func(a *Argument, S *Expr[Set[Real]]) {
			identity := a.TermAs[Fun[Real, Real]]("λx:real. x")
			density := a.TermAs[Fun[Real, Real]]("normal_density(&0, &1)")
			a.Show(
				"products of the identity and the density are continuous",
				By(
					real_continuous.ContinuousOnId.At(S),
					At(std.continuous, S),
					real_continuous.ContinuousOnMul.At(identity, density, S),
					real_continuous.ContinuousOnMul.At(identity, identity, S),
					real_continuous.ContinuousOnMul.At(a.TermAs[Fun[Real, Real]]("λx:real. x * x"), density, S)))
		})
	std.negativeDerivative = ctx.Lemma("∀x:real. "+
		"    real_derivative_at(λy:real. -normal_density(&0, &1, y), x, x * normal_density(&0, &1, x))",
		func(a *Argument, x *Expr[Real]) {
			a.Show(
				"negate the derivative of the density",
				ByArith(
					At(std.derivative, x),
					real_derivative.DerivativeNeg.At(
						a.TermAs[Fun[Real, Real]]("normal_density(&0, &1)"),
						x,
						a.TermAs[Real]("-x * normal_density(&0, &1, x)"))))
		})
	std.windows = ctx.Lemma(Statement{
		Binders: "∀f:(real → real).",
		Hypotheses: []string{
			"real_continuous_on(𝕌, f)",
			"∀x:real. &0 ≤ f(x)",
		},
		Conclusion: "(∀n:num. &0 ≤ real_integral(f, -&n, &n)) ∧ " +
			"(∀n:num. real_integral(f, -&n, &n) ≤ real_integral(f, -&(n + 1), &(n + 1))) ∧ " +
			"nonneg_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, λx:real. extended_of_real(f(x))) = " +
			"extended_sup(image(λn:num. extended_of_real(real_integral(f, -&n, &n)), 𝕌))",
	}, func(a *Argument, f *Arrow[Real, Real], continuous, nonnegative Fact) {
		line := a.TermAs[Set[Real]]("𝕌")
		piece := a.Have(
			"over an ordered interval f has a nonnegative integral",
			"∀p q:real. p ≤ q ⇒ &0 ≤ real_integral(f, p, q)",
			Derive(func(b *Argument) {
				p := b.FixAs[Real]("p")
				q := b.FixAs[Real]("q")
				order := b.Assume()
				interval := b.TermAs[Set[Real]]("⟦p, q⟧")
				b.Show(
					"f has its integral there, and a nonnegative function a nonnegative one",
					By(
						order,
						continuous,
						nonnegative,
						set_order.SubsetUniv.At(interval),
						real_continuous.ContinuousOnSubset.At(f, line, interval),
						real_integral.ContinuousHasIntegral.At(f, p, q),
						real_integral.RiemannIntegralNonneg.At(f, p, q, b.TermAs[Real]("real_integral(f, p, q)"))))
			}))
		a.Show(
			"the windows grow by nonnegative end pieces, and their supremum is the integral over the line",
			SplitConjAll(
				Case(
					"each window integral is nonnegative",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.Show(
							"the window ⟦−n, n⟧ is ordered",
							ByArith(real_order_ring.NumNonneg.At(n), piece.At(b.TermAs[Real]("-&n"), b.TermAs[Real]("&n"))))
					})),
				Case(
					"the next window adds two nonnegative end pieces",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						inner, outer := b.TermAs[Real]("&n"), b.TermAs[Real]("&(n + 1)")
						innerLeft, outerLeft := b.TermAs[Real]("-&n"), b.TermAs[Real]("-&(n + 1)")
						bigger := b.TermAs[Set[Real]]("⟦-&(n + 1), &(n + 1)⟧")
						b.Show(
							"split ⟦−(n + 1), n + 1⟧ at −n and n",
							ByArith(
								real_order_ring.NumNonneg.At(n),
								real_construction.OfNumAdd.At(n, b.TermAs[Nat]("1")),
								piece.At(outerLeft, innerLeft),
								piece.At(inner, outer),
								continuous,
								set_order.SubsetUniv.At(bigger),
								real_continuous.ContinuousOnSubset.At(f, line, bigger),
								real_integral.IntegralAdditive.At(f, outerLeft, outer, outerLeft, innerLeft, inner),
								real_integral.IntegralAdditive.At(f, outerLeft, outer, outerLeft, inner, outer)))
					})),
				Case(
					"the windows are the symmetric windows about 0 with step 1",
					ByArith(
						continuous,
						nonnegative,
						real_order_ring.ZeroLessThanOne,
						lebesgue_riemann.LebesgueNonnegIntegralBySymmetricWindows.At(
							f, a.TermAs[Real]("&0"), a.TermAs[Real]("&1"))))))
	})
	std.powersMeasurable = ctx.Lemma("real_measurable(𝕌, borel_sets(real_topology), λx:real. x) ∧ "+
		"real_measurable(𝕌, borel_sets(real_topology), λx:real. x * x)",
		func(a *Argument) {
			line := a.TermAs[Set[Real]]("𝕌")
			borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
			identity := a.TermAs[Fun[Real, Real]]("λx:real. x")
			a.Show(
				"the identity is Borel measurable, and so is its square",
				By(
					borel_function.LineBorelSigmaAlgebra,
					measurable_function.RealMeasurableSquare.At(line, borel, identity),
					borel_function.RealMeasurableIdentity))
		})
	std.transport = ctx.Lemma(Statement{
		Binders: "∀f:(real → real).",
		Hypotheses: []string{
			"real_measurable(𝕌, borel_sets(real_topology), f)",
		},
		Conclusion: "(real_integrable(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), f) ⇔ " +
			"    real_integrable(𝕌, " +
			"        «lebesgueSets», " +
			"        lebesgue_outer_measure, " +
			"        λx:real. normal_density(&0, &1, x) * f(x))) ∧ " +
			"expectation(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), f) = " +
			"measure_integral(𝕌, " +
			"    «lebesgueSets», " +
			"    lebesgue_outer_measure, " +
			"    λx:real. normal_density(&0, &1, x) * f(x))",
	}, func(a *Argument, f *Arrow[Real, Real], borelMeasurable Fact) {
		line := a.TermAs[Set[Real]]("𝕌")
		borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
		lebesgue := a.TermAs[Set[Set[Real]]]("«lebesgueSets»")
		μ := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("lebesgue_outer_measure")
		ν := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("«densityMeasure»")
		density := a.TermAs[Fun[Real, Real]]("normal_density(&0, &1)")
		zero, one := a.TermAs[Real]("&0"), a.TermAs[Real]("&1")
		inclusion := a.Have(
			"Borel sets are Lebesgue measurable",
			"borel_sets(real_topology) ⊆ «lebesgueSets»",
			BySets(lebesgue_measure.MeasurableBorel))
		densityMeasurable := a.Have(
			"φ, continuous on the line, is Lebesgue measurable",
			"real_measurable(𝕌, «lebesgueSets», normal_density(&0, &1))",
			By(At(std.continuous, line), lebesgue_integral.ContinuousLebesgueMeasurable.At(density)))
		lebesgueMeasurable := a.Have(
			"and so is the Borel f",
			"real_measurable(𝕌, «lebesgueSets», f)",
			By(
				borelMeasurable,
				inclusion,
				measurable_function.RealMeasurableSourceMono.At(line, borel, lebesgue, f)))
		measure := a.Have(
			"φ is the density of a measure on the Lebesgue sets",
			"measure_on(𝕌, «lebesgueSets», «densityMeasure»)",
			By(
				densityMeasurable,
				lebesgue_measure.LebesgueMeasureOn,
				lebesgue_measure.LebesgueSigmaAlgebra,
				measurable_function.ExtendedMeasurableOfReal.At(line, lebesgue, density),
				density_measure.DensityMeasure.At(
					line,
					lebesgue,
					μ,
					a.TermAs[Fun[Real, extended_nonneg_real.ExtendedNonnegReal]](
						"λx:real. extended_of_real(normal_density(&0, &1, x))"))))
		law := a.Have(
			"the standard normal is that measure",
			"normal_distribution(&0, &1) = «densityMeasure»",
			Funext(),
			Derive(func(b *Argument) {
				E := b.FixAs[Set[Real]]("E")
				b.Show(
					"read the distribution at E",
					By(normal_distribution.NormalDistributionDef.At(zero, one, E)))
			}))
		againstLebesgue := a.Have(
			"against the density measure f integrates as φ·f against Lebesgue measure",
			"(real_integrable(𝕌, «lebesgueSets», «densityMeasure», f) ⇔ "+
				"    real_integrable(𝕌, "+
				"        «lebesgueSets», "+
				"        lebesgue_outer_measure, "+
				"        λx:real. normal_density(&0, &1, x) * f(x))) ∧ "+
				"measure_integral(𝕌, «lebesgueSets», «densityMeasure», f) = "+
				"measure_integral(𝕌, "+
				"    «lebesgueSets», "+
				"    lebesgue_outer_measure, "+
				"    λx:real. normal_density(&0, &1, x) * f(x))",
			By(
				lebesgueMeasurable,
				densityMeasurable,
				lebesgue_measure.LebesgueMeasureOn,
				std.nonnegative,
				density_measure.DensityMeasureIntegral.At(line, lebesgue, μ, density, f)))
		onBorel := a.Have(
			"and the Borel f integrates on the Borel sets as on the Lebesgue sets",
			"(real_integrable(𝕌, borel_sets(real_topology), «densityMeasure», f) ⇔ "+
				"    real_integrable(𝕌, «lebesgueSets», «densityMeasure», f)) ∧ "+
				"measure_integral(𝕌, borel_sets(real_topology), «densityMeasure», f) = "+
				"measure_integral(𝕌, «lebesgueSets», «densityMeasure», f)",
			By(
				measure,
				borelMeasurable,
				inclusion,
				borel_function.LineBorelSigmaAlgebra,
				measure_integral.SubSigmaRealIntegral.At(line, lebesgue, ν, borel, f)))
		a.Show(
			"so the expectation is the Lebesgue integral of φ·f",
			By(
				law,
				onBorel,
				againstLebesgue,
				probability_space.ExpectationDef.At(
					line,
					borel,
					a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("normal_distribution(&0, &1)"),
					f)))
	})
	return std
}
