package weak_convergence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/borel_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// WeakConvergenceSmoothTests — probabilities ν(n) on the line converge weakly
// to a measure ρ once their integrals converge at every function with three
// bounded derivatives: the constant 1 makes ρ a probability; three moving
// averages bring such a function uniformly within ε of a bounded uniformly
// continuous test; and a bounded continuous test, clipped to a window that
// holds all but δ of ρ's mass, is uniformly continuous, the part outside the
// window held by a cutoff whose integrals converge as well.
var WeakConvergenceSmoothTests = weakConvergenceSmoothTestsThm{family.Add(registry.ProofEntry{
	Name: "WeakConvergenceSmoothTests",
	Key:  "prop_2b254ae482a0b973",
	Reading: "D is a tower of derivatives, D(k + 1) the derivative of D(k) for k ≤ 2, and the " +
		"test function is D(0): three times differentiable, bounded with its three derivatives. " +
		"Of ρ only a measure on the Borel sets is asked: the constant test function forces its " +
		"mass to be 1, and a limit of mass 1 keeps the ν(n) from losing mass to infinity.",
	Build: family.Sections(Statement{
		Binders: "∀ν:(num → set(real) → extended_nonneg_real). ∀ρ:(set(real) → extended_nonneg_real).",
		Hypotheses: []string{
			"∀n:num. probability_on(𝕌, borel_sets(real_topology), ν(n))",
			"measure_on(𝕌, borel_sets(real_topology), ρ)",
			"∀D:(num → real → real). " +
				"    (∀k:num. ∀y:real. k ≤ 2 ⇒ real_derivative_at(D(k), y, D(k + 1)(y))) ∧ " +
				"    (∃B:real. ∀k:num. ∀y:real. k ≤ 3 ⇒ |D(k)(y)| ≤ B) ⇒ " +
				"    (λn:num. expectation(𝕌, borel_sets(real_topology), ν(n), D(0))) ⟶ " +
				"    expectation(𝕌, borel_sets(real_topology), ρ, D(0))",
		},
		Conclusion: "weakly_converges(real_topology, ν, ρ)",
		Abbrev: Abbrev{
			{Name: "boundedTower", Text: "λD:(num → real → real). " +
				"    (∀k:num. ∀y:real. k ≤ 2 ⇒ real_derivative_at(D(k), y, D(k + 1)(y))) ∧ " +
				"    (∃B:real. ∀k:num. ∀y:real. k ≤ 3 ⇒ |D(k)(y)| ≤ B)"},
			{Name: "clip", Text: "λa:real. λb:real. λx:real. max(a, min(b, x))"},
			{Name: "lineMeasure", Text: "λμ:(set(real) → extended_nonneg_real). " +
				"    measure_on(𝕌, borel_sets(real_topology), μ)"},
			{Name: "indicator", Text: "λE:set(real). λc:real. λx:real. COND(x ∈ E, c, &0)"},
			{Name: "boundedBy", Text: "λf:(real → real). λB:real. ∀x:real. |f(x)| ≤ B"},
			{Name: "convergesFor", Text: "λν:(num → set(real) → extended_nonneg_real). " +
				"λρ:(set(real) → extended_nonneg_real). " +
				"λf:(real → real). " +
				"    (λn:num. «lineIntegral»(ν(n),f)) ⟶ «lineIntegral»(ρ,f)"},
			{Name: "smoothConverges", Text: "λν:(num → set(real) → extended_nonneg_real). " +
				"λρ:(set(real) → extended_nonneg_real). " +
				"∀D:(num → real → real). " +
				"    «boundedTower»(D) ⇒ «convergesFor»(ν,ρ,D(0))"},
			{Name: "cutoff", Text: "λK:real. λx:real. «clip»(&0, &1, K + &1 - |x|)"},
			{Name: "window", Text: "λK:real. ⟦-K, K⟧"},
			{Name: "clippedTest", Text: "λf:(real → real). λK:real. λx:real. f(«clip»(-(K + &1), K + &1, x))"},
			{Name: "tailEnvelope", Text: "λB:real. λK:real. λx:real. &2 * B * (&1 - «cutoff»(K,x))"},
			{Name: "growingWindow", Text: "λn:num. «window»(&n)"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			indicatorIntegral := ctx.Lemma(Statement{
				Binders: "∀μ:(set(real) → extended_nonneg_real). ∀E:set(real).",
				Hypotheses: []string{
					"«lineMeasure»(μ)",
					"E ∈ borel_sets(real_topology)",
				},
				Conclusion: "«lineIntegral»(μ, λx:real. «indicator»(E, &1, x)) = extended_to_real(μ(E))",
			},
				func(
					a *Argument,
					μ *Arrow[Set[Real], ExtendedNonnegReal],
					E *Expr[Set[Real]],
					measure, borel Fact,
				) {
					a.Show(
						"the indicator of a Borel set integrates to its measure",
						ByArith(
							measure,
							borel,
							measure_integral.IntegralIndicator.At(
								a.TermAs[Set[Real]]("𝕌"),
								a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"),
								μ,
								E,
								a.TermAs[Real]("&1"))),
					)
				})

			integralComparison := ctx.Lemma(Statement{
				Binders: "∀μ:((real → bool) → extended_nonneg_real). ∀f g h:(real → real).",
				Hypotheses: []string{
					"«lineMeasure»(μ)",
					"«lineIntegrable»(μ, f)",
					"«lineIntegrable»(μ, g)",
					"«lineIntegrable»(μ, h)",
					"∀x:real. |f(x) - g(x)| ≤ h(x)",
				},
				Conclusion: "|«lineIntegral»(μ, f) - «lineIntegral»(μ, g)| ≤ «lineIntegral»(μ, h)",
			},
				func(a *Argument, μ *Arrow[Set[Real], ExtendedNonnegReal], f, g, h *Arrow[Real, Real],
					measure, integrableF, integrableG, integrableH, dominated Fact) {
					a.Show(
						"integrals differ by at most the integral of a bound on the difference",
						By(
							measure,
							integrableF,
							integrableG,
							integrableH,
							dominated,
							measure_integral.IntegralAbsSubLe.At(
								a.TermAs[Set[Real]]("𝕌"), a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"), μ, f, g, h)),
					)
				})

			// The constant c as a tower: c at k = 0 and 0 above, each a constant with derivative 0.
			constantTower := ctx.Lemma("∀c:real. "+
				"    (∀k:num. ∀y:real. "+
				"        k ≤ 2 ⇒ real_derivative_at(λx:real. COND(k = 0, c, &0), y, COND(k + 1 = 0, c, &0))) ∧ "+
				"    (∃B:real. ∀k:num. ∀y:real. k ≤ 3 ⇒ |COND(k = 0, c, &0)| ≤ B) ∧ "+
				"    (λx:real. COND(0 = 0, c, &0)) = λx:real. c",
				func(a *Argument, c *Expr[Real]) {
					bottom := a.Have(
						"at k = 0 the tower is the constant c",
						"(λk:num. λx:real. COND(k = 0, c₀, &0))(0) = λx:real. c₀",
						ByArith(Raw),
					)
					steps := a.Have(
						"each function of the tower is a constant, with derivative 0, the next function",
						Statement{
							Binders: "∀k:num. ∀y:real.",
							Hypotheses: []string{
								"k ≤ 2",
							},
							Conclusion: "real_derivative_at(λx:real. COND(k = 0, c₀, &0), y, COND(k + 1 = 0, c₀, &0))",
						},
						Derive(func(b *Argument) {
							b.FixAs[Nat]()
							y := b.FixAs[Real]()
							b.Assume()
							above := b.Have(
								"above 0 the tower is 0",
								"COND(k₀ + 1 = 0, c₀, &0) = &0",
								ByArith(Raw),
							)
							slope := b.Have(
								"a constant has derivative 0",
								"real_derivative_at(λx:real. COND(k₀ = 0, c₀, &0), y₀, &0)",
								By(real_derivative.DerivativeConst.At(b.TermAs[Real]("COND(k₀ = 0, c₀, &0)"), y)),
							)
							b.Show(
								"so the step holds",
								By(above, slope),
							)
						}),
					)
					bound := a.Have(
						"|c| bounds the tower",
						"∃B:real. ∀k:num. ∀y:real. k ≤ 3 ⇒ |COND(k = 0, c₀, &0)| ≤ B",
						Witness(a.TermAs[Real]("|c₀|")),
						StripQuant(),
						StripImp(),
						ByArith(real_sgn_abs.AbsNonneg.At(c), real_sgn_abs.AbsOfZero),
					)
					a.Show(
						"the constant tower's steps, its bound and its start",
						By(steps, bound, bottom),
					)
				})

			lineMeasurableCarrier := ctx.Lemma("𝕌 ∈ borel_sets(real_topology)",
				func(a *Argument) {
					a.Show(
						"the Borel sets form a σ-algebra on the points of the line, which holds the line",
						By(
							sigma_algebra.SigmaAlgebraOnDef.At(
								a.TermAs[Set[Real]]("𝕌"), a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")),
							borel_function.LineBorelSigmaAlgebra))
				})

			indicatorOnLine := ctx.Lemma("∀c:real. (λx:real. «indicator»(𝕌, c, x)) = λx:real. c",
				func(a *Argument, c *Expr[Real]) {
					a.Do(Funext())
					x := a.FixAs[Real]()
					a.Show(
						"every point lies in the line",
						By(set_basic.InUniv.At(x)),
					)
				})

			constantOneIntegral := ctx.Lemma(Statement{
				Binders: "∀μ:(set(real) → extended_nonneg_real).",
				Hypotheses: []string{
					"«lineMeasure»(μ)",
				},
				Conclusion: "«lineIntegral»(μ, λx:real. &1) = extended_to_real(μ(𝕌))",
			},
				func(a *Argument, μ *Arrow[Set[Real], ExtendedNonnegReal], measure Fact) {
					indicator := a.Have(
						"the indicator of the line, a Borel set, integrates to the measure of the line",
						"«lineIntegral»(μ₀, λx:real. «indicator»(𝕌, &1, x)) = extended_to_real(μ₀(𝕌))",
						By(measure, lineMeasurableCarrier, At(indicatorIntegral, μ, a.TermAs[Set[Real]]("𝕌"))),
					)
					a.Show(
						"and that indicator is the constant 1",
						By(indicator, At(indicatorOnLine, a.TermAs[Real]("&1"))),
					)
				})

			continuousIntegrable := ctx.Lemma(Statement{
				Binders: "∀μ:((real → bool) → extended_nonneg_real). ∀f:(real → real). ∀B:real.",
				Hypotheses: []string{
					"«lineProbability»(μ)",
					"real_continuous_on(𝕌, f)",
					"«boundedBy»(f, B)",
				},
				Conclusion: "«lineIntegrable»(μ, f)",
			},
				func(a *Argument, μ *Arrow[Set[Real], ExtendedNonnegReal], f *Arrow[Real, Real], B *Expr[Real],
					probability, continuous, bounded Fact) {
					measurable := a.Have(
						"a function continuous on the line is Borel measurable",
						"real_measurable(𝕌, borel_sets(real_topology), f₀)",
						By(continuous, borel_function.ContinuousBorelMeasurable.At(f)),
					)
					a.Show(
						"and bounded, it is integrable against a probability",
						By(
							probability,
							measurable,
							bounded,
							probability_space.BoundedIntegrable.At(
								a.TermAs[Set[Real]]("𝕌"), a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"), μ, f, B)),
					)
				})

			uniformIntegralComparison := ctx.Lemma(Statement{
				Binders: "∀μ:((real → bool) → extended_nonneg_real). ∀f g:(real → real). ∀e:real.",
				Hypotheses: []string{
					"«lineProbability»(μ)",
					"«lineIntegrable»(μ, f)",
					"«lineIntegrable»(μ, g)",
					"«boundedBy»(λx:real. f(x) - g(x), e)",
				},
				Conclusion: "|«lineIntegral»(μ, f) - «lineIntegral»(μ, g)| ≤ e",
			},
				func(a *Argument, μ *Arrow[Set[Real], ExtendedNonnegReal], f, g *Arrow[Real, Real], e *Expr[Real],
					probability, integrableF, integrableG, near Fact) {
					constant := a.Have(
						"against a probability the constant e is integrable, with integral e",
						"«lineIntegrable»(μ₀, λx:real. e₀) ∧ «lineIntegral»(μ₀, λx:real. e₀) = e₀",
						By(
							Normalized,
							probability,
							probability_space.ExpectationConstant.At(
								a.TermAs[Set[Real]]("𝕌"), a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"), μ, e),
							probability_space.ExpectationDef.At(
								a.TermAs[Set[Real]]("𝕌"),
								a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"),
								μ,
								a.TermAs[Fun[Real, Real]]("λx:real. e₀"))),
					)
					comparison := a.Have(
						"so the integrals of f and g differ by at most the integral of e",
						"|«lineIntegral»(μ₀, f₀) - «lineIntegral»(μ₀, g₀)| ≤ «lineIntegral»(μ₀, λx:real. e₀)",
						By(
							probability,
							integrableF,
							integrableG,
							near,
							constant,
							probability_space.ProbabilityOnDef.At(
								a.TermAs[Set[Real]]("𝕌"), a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"), μ),
							measure_integral.IntegralAbsSubLe.At(
								a.TermAs[Set[Real]]("𝕌"),
								a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"),
								μ,
								f,
								g,
								a.TermAs[Fun[Real, Real]]("λx:real. e₀"))),
					)
					a.Show(
						"that is, by at most e",
						By(constant, comparison),
					)
				})

			threeTermError := ctx.Lemma(Statement{
				Binders: "∀a b c d e₁ e₂ e₃:real.",
				Hypotheses: []string{
					"|a - b| ≤ e₁",
					"|b - c| < e₂",
					"|c - d| ≤ e₃",
				},
				Conclusion: "|a - d| < e₁ + e₂ + e₃",
			},
				func(arg *Argument, a, b, c, d, e1, e2, e3 *Expr[Real], first, second, third Fact) {
					steps := arg.Have(
						"a − d is the sum of the three steps",
						"a₀ - d₀ = a₀ - b₀ + (b₀ - c₀) + (c₀ - d₀)",
						ByArith(Raw),
					)
					firstTwo := arg.Have(
						"the triangle inequality on the first two steps",
						"|a₀ - b₀ + (b₀ - c₀)| ≤ |a₀ - b₀| + |b₀ - c₀|",
						By(real_sgn_abs.AbsTriangle.At(arg.TermAs[Real]("a₀ - b₀"), arg.TermAs[Real]("b₀ - c₀"))),
					)
					all := arg.Have(
						"and with the third",
						"|a₀ - d₀| ≤ |a₀ - b₀ + (b₀ - c₀)| + |c₀ - d₀|",
						By(
							steps,
							real_sgn_abs.AbsTriangle.At(arg.TermAs[Real]("a₀ - b₀ + (b₀ - c₀)"), arg.TermAs[Real]("c₀ - d₀"))),
					)
					arg.Show(
						"so |a − d| < e₁ + e₂ + e₃",
						ByArith(Raw, all, firstTwo, first, second, third),
					)
				})

			towerBase := ctx.Lemma(Statement{
				Binders: "∀D:(num → real → real).",
				Hypotheses: []string{
					"«boundedTower»(D)",
				},
				Conclusion: "real_continuous_on(𝕌, D(0)) ∧ (∃B:real. «boundedBy»(D(0), B))",
			},
				func(a *Argument, D *Arrow[Nat, Fun[Real, Real]], tower Fact) {
					firstStep := a.Have(
						"0 is a step of the tower",
						"0 ≤ 2",
						ByArith(Raw),
					)
					slope := a.Have(
						"so D(0) has D(1) as its derivative everywhere",
						"∀x:real. x ∈ 𝕌 ⇒ real_derivative_at(D₀(0), x, D₀(0 + 1, x))",
						Derive(func(b *Argument) {
							b.FixAs[Real]()
							b.Assume()
							b.Show(
								"the tower's first step at x",
								By(tower, firstStep),
							)
						}),
					)
					continuity := a.Have(
						"and is continuous",
						"real_continuous_on(𝕌, D₀(0))",
						By(
							slope,
							real_derivative.DerivativeContinuousOn.At(
								a.TermAs[Fun[Real, Real]]("D₀(0)"),
								a.TermAs[Fun[Real, Real]]("D₀(0 + 1)"),
								a.TermAs[Set[Real]]("𝕌"))),
					)
					M, towerBound := a.ObtainAs[Real](
						"the tower has a bound M",
						"∃M:real. ∀k:num. ∀y:real. k ≤ 3 ⇒ |D₀(k, y)| ≤ M",
						By(tower),
					)
					bottomLevel := a.Have(
						"0 is a level of the tower",
						"0 ≤ 3",
						ByArith(Raw),
					)
					bounded := a.Have(
						"so M bounds D(0)",
						"∃B:real. «boundedBy»(D₀(0), B)",
						Witness(M),
						Derive(func(b *Argument) {
							b.FixAs[Real]()
							b.Show(
								"M bounds the tower at level 0",
								By(bottomLevel, towerBound),
							)
						}),
					)
					a.Show(
						"D(0) is continuous and bounded",
						By(continuity, bounded),
					)
				})

			// A bounded uniformly continuous test f is within ε/4 of the bottom D(0) of a smooth
			// tower. Under every probability the integrals of f and D(0) are then within ε/4, and
			// those of D(0) converge: so from some index on those of f are within 3ε/4 of their limit.
			uniformTestConvergence := ctx.Lemma(Statement{
				Binders: "∀ν:(num → (real → bool) → extended_nonneg_real). " +
					"∀ρ:((real → bool) → extended_nonneg_real). " +
					"∀f:(real → real). " +
					"∀B:real.",
				Hypotheses: []string{
					"∀n:num. «lineProbability»(ν(n))",
					"«lineProbability»(ρ)",
					"«smoothConverges»(ν, ρ)",
					"real_uniformly_continuous_on(𝕌, f)",
					"«boundedBy»(f, B)",
				},
				Conclusion: "«convergesFor»(ν, ρ, f)",
			},
				func(
					a *Argument,
					ν *Arrow[Nat, Fun[Set[Real], ExtendedNonnegReal]],
					ρ *Arrow[Set[Real], ExtendedNonnegReal],
					f *Arrow[Real, Real],
					B *Expr[Real],
					probabilities, probability, smoothTests, uniform, bounded Fact,
				) {
					continuous := a.Have(
						"f is continuous",
						"real_continuous_on(𝕌, f₀)",
						By(uniform, real_continuous.UniformlyContinuousContinuous.At(f, a.TermAs[Set[Real]]("𝕌"))),
					)
					eventually := a.Have(
						"for every ε > 0, from some index on the integrals of f are within ε of their limit",
						Statement{
							Binders: "∀ε:real.",
							Hypotheses: []string{
								"&0 < ε",
							},
							Conclusion: "∃N:num. ∀n:num. N ≤ n ⇒ |«lineIntegral»(ν₀(n), f₀) - «lineIntegral»(ρ₀, f₀)| < ε",
						},
						Derive(func(b *Argument) {
							b.FixAs[Real]()
							pos := b.Assume()
							quarter := b.Have(
								"ε/4 is positive",
								"&0 < ε₀ / &4",
								ByArith(Raw, pos),
							)
							D, approximation := b.ObtainAs[Fun2[Nat, Real, Real]](
								"a smooth tower D has its bottom within ε/4 of f",
								"∃D:(num → real → real). «boundedTower»(D) ∧ «boundedBy»(λx:real. D(0, x) - f₀(x), ε₀ / &4)",
								By(
									uniform,
									bounded,
									quarter,
									real_integral.UniformSmoothApproximation.At(f, B, b.TermAs[Real]("ε₀ / &4"))),
							)
							bottom := b.Have(
								"its bottom D(0) is continuous and bounded",
								"real_continuous_on(𝕌, D₀(0)) ∧ (∃C:real. «boundedBy»(D₀(0), C))",
								By(approximation, At(towerBase, D)),
							)
							bottomContinuous := b.Have(
								"D(0) is continuous",
								"real_continuous_on(𝕌, D₀(0))",
								By(bottom),
							)
							C, bottomBounded := b.ObtainAs[Real](
								"and bounded by some C",
								"∃C:real. «boundedBy»(D₀(0), C)",
								By(bottom),
							)
							reversed := b.Have(
								"f is within ε/4 of D(0)",
								"«boundedBy»(λx:real. f₀(x) - D₀(0, x), ε₀ / &4)",
								By(Normalized, approximation, real_sgn_abs.AbsSubComm),
							)
							bottomConverges := b.Have(
								"the integrals of D(0) converge, D being a tower of three bounded derivatives",
								"«convergesFor»(ν₀, ρ₀, D₀(0))",
								By(smoothTests, approximation),
							)
							near := b.Have(
								"under every probability the integrals of f and D(0) are within ε/4",
								Statement{
									Binders: "∀μ:((real → bool) → extended_nonneg_real).",
									Hypotheses: []string{
										"«lineProbability»(μ)",
									},
									Conclusion: "|«lineIntegral»(μ, f₀) - «lineIntegral»(μ, D₀(0))| ≤ ε₀ / &4",
								},
								Derive(func(c *Argument) {
									μ := c.FixAs[Fun[Set[Real], ExtendedNonnegReal]]()
									probabilityμ := c.Assume()
									integrableF := c.Have(
										"f is integrable",
										"«lineIntegrable»(μ₀, f₀)",
										By(probabilityμ, continuous, bounded, At(continuousIntegrable, μ, f, B)),
									)
									integrableD := c.Have(
										"and so is D(0)",
										"«lineIntegrable»(μ₀, D₀(0))",
										By(
											probabilityμ,
											bottomContinuous,
											bottomBounded,
											At(continuousIntegrable, μ, c.TermAs[Fun[Real, Real]]("D₀(0)"), C)),
									)
									c.Show(
										"so their integrals differ by at most ε/4",
										By(
											probabilityμ,
											integrableF,
											integrableD,
											reversed,
											At(
												uniformIntegralComparison,
												μ,
												f,
												c.TermAs[Fun[Real, Real]]("D₀(0)"),
												c.TermAs[Real]("ε₀ / &4"))),
									)
								}),
							)
							M, tail := b.ObtainAs[Nat](
								"from some index M on the integrals of D(0) are within ε/4 of their limit",
								"∃M:num. ∀n:num. M ≤ n ⇒ |«lineIntegral»(ν₀(n), D₀(0)) - «lineIntegral»(ρ₀, D₀(0))| < ε₀ / &4",
								By(
									bottomConverges,
									quarter,
									real_sequences.RealConvergesToDef.At(
										b.TermAs[Fun[Nat, Real]]("λn:num. «lineIntegral»(ν₀(n), D₀(0))"),
										b.TermAs[Real]("«lineIntegral»(ρ₀, D₀(0))"))),
							)
							b.Show(
								"past M the integrals of f are within 3ε/4 of their limit",
								Witness(M),
								Derive(func(c *Argument) {
									c.FixAs[Nat]()
									late := c.Assume()
									underNu := c.Have(
										"under ν(n) the integrals of f and D(0) are within ε/4",
										"|«lineIntegral»(ν₀(n₀), f₀) - «lineIntegral»(ν₀(n₀), D₀(0))| ≤ ε₀ / &4",
										By(probabilities, near),
									)
									underRho := c.Have(
										"and so are they under ρ",
										"|«lineIntegral»(ρ₀, f₀) - «lineIntegral»(ρ₀, D₀(0))| ≤ ε₀ / &4",
										By(probability, near),
									)
									underRhoReversed := c.Have(
										"read from D(0) to f",
										"|«lineIntegral»(ρ₀, D₀(0)) - «lineIntegral»(ρ₀, f₀)| ≤ ε₀ / &4",
										By(
											underRho,
											real_sgn_abs.AbsSubComm.At(
												c.TermAs[Real]("«lineIntegral»(ρ₀, D₀(0))"),
												c.TermAs[Real]("«lineIntegral»(ρ₀, f₀)"))),
									)
									smoothGap := c.Have(
										"past M the integrals of D(0) are within ε/4 of their limit",
										"|«lineIntegral»(ν₀(n₀), D₀(0)) - «lineIntegral»(ρ₀, D₀(0))| < ε₀ / &4",
										By(tail, late),
									)
									total := c.Have(
										"so the three gaps add up to less than 3ε/4",
										"|«lineIntegral»(ν₀(n₀), f₀) - «lineIntegral»(ρ₀, f₀)| < ε₀ / &4 + ε₀ / &4 + ε₀ / &4",
										By(
											underNu,
											smoothGap,
											underRhoReversed,
											At(
												threeTermError,
												c.TermAs[Real]("«lineIntegral»(ν₀(n₀), f₀)"),
												c.TermAs[Real]("«lineIntegral»(ν₀(n₀), D₀(0))"),
												c.TermAs[Real]("«lineIntegral»(ρ₀, D₀(0))"),
												c.TermAs[Real]("«lineIntegral»(ρ₀, f₀)"),
												c.TermAs[Real]("ε₀ / &4"),
												c.TermAs[Real]("ε₀ / &4"),
												c.TermAs[Real]("ε₀ / &4"))),
									)
									c.Show(
										"which is less than ε",
										ByArith(Raw, total, pos),
									)
								}),
							)
						}),
					)
					a.Show(
						"so the integrals of f converge to the one under ρ",
						By(
							eventually,
							real_sequences.RealConvergesToDef.At(
								a.TermAs[Fun[Nat, Real]]("λn:num. «lineIntegral»(ν₀(n), f₀)"),
								a.TermAs[Real]("«lineIntegral»(ρ₀, f₀)"))),
					)
				})

			cutoffProperties := ctx.Lemma("∀K x:real. "+
				"    &0 ≤ «cutoff»(K, x) ∧ "+
				"    «cutoff»(K, x) ≤ &1 ∧ "+
				"    (|x| ≤ K ⇒ «cutoff»(K, x) = &1) ∧ "+
				"    (K + &1 ≤ |x| ⇒ «cutoff»(K, x) = &0)",
				func(a *Argument, K, x *Expr[Real]) {
					zero := a.TermAs[Real]("&0")
					one := a.TermAs[Real]("&1")
					room := a.TermAs[Real]("K₀ + &1 - |x₀|")
					a.Show(
						"K + 1 − |x| clamped to [0, 1] lies in [0, 1], is 1 for |x| ≤ K and 0 for |x| ≥ K + 1",
						ByArith(real_sup_inf.ClampRange.At(zero, one, room), real_sup_inf.ClampEnds.At(zero, one, room)),
					)
				})

			// Clipping to the window changes f only where |x| > K + 1, where the cutoff is 0, and there
			// both f and its clipped copy are within B of 0: so 2B(1 − cutoff) bounds the difference.
			cutoffError := ctx.Lemma(Statement{
				Binders: "∀f:(real → real). ∀K B:real.",
				Hypotheses: []string{
					"&0 ≤ K",
					"&0 ≤ B",
					"«boundedBy»(f, B)",
				},
				Conclusion: "∀x:real. |f(x) - «clippedTest»(f, K, x)| ≤ «tailEnvelope»(B, K, x)",
			},
				func(a *Argument, f *Arrow[Real, Real], K, B *Expr[Real], nonnegK, nonnegB, bounded Fact) {
					x := a.FixAs[Real]()
					cutoff := a.Have(
						"the cutoff lies in [0, 1], is 1 on ⟦−K, K⟧ and 0 off ⟦−K − 1, K + 1⟧",
						"&0 ≤ «cutoff»(K₀, x₀) ∧ "+
							"«cutoff»(K₀, x₀) ≤ &1 ∧ "+
							"(|x₀| ≤ K₀ ⇒ «cutoff»(K₀, x₀) = &1) ∧ "+
							"(K₀ + &1 ≤ |x₀| ⇒ «cutoff»(K₀, x₀) = &0)",
						By(At(cutoffProperties, K, x)),
					)
					envelopeNonneg := a.Have(
						"so the tail envelope is nonnegative",
						"&0 ≤ «tailEnvelope»(B₀, K₀, x₀)",
						ByArith(Raw, nonnegB, cutoff),
					)
					a.Cases(a.TermAs[Bool]("|x₀| ≤ K₀ + &1"))
					a.When(
						"inside the window clipping changes nothing",
						func(b *Argument, inside Fact) {
							wide := b.Have(
								"the window ⟦−(K + 1), K + 1⟧ is not empty",
								"-(K₀ + &1) ≤ K₀ + &1",
								ByArith(Raw, nonnegK),
							)
							between := b.Have(
								"x lies in the window",
								"-(K₀ + &1) ≤ x₀ ∧ x₀ ≤ K₀ + &1",
								By(inside, real_sgn_abs.AbsBounds.At(x, b.TermAs[Real]("K₀ + &1"))),
							)
							fixed := b.Have(
								"so clipping fixes x",
								"«clip»(-(K₀ + &1), K₀ + &1, x₀) = x₀",
								By(
									wide,
									between,
									real_sup_inf.ClampRange.At(b.TermAs[Real]("-(K₀ + &1)"), b.TermAs[Real]("K₀ + &1"), x)),
							)
							unchanged := b.Have(
								"and the difference is 0",
								"|f₀(x₀) - «clippedTest»(f₀, K₀, x₀)| = &0",
								By(fixed, real_ring.SubRefl, real_sgn_abs.AbsOfZero),
							)
							b.Show(
								"which the nonnegative envelope bounds",
								By(envelopeNonneg, unchanged),
							)
						})
					a.Otherwise(
						"outside the window the cutoff is 0 and both values are within B of 0",
						func(b *Argument, outside Fact) {
							far := b.Have(
								"|x| ≥ K + 1",
								"K₀ + &1 ≤ |x₀|",
								ByArith(outside, real_order_ring.NotLessEq.At(b.TermAs[Real]("K₀ + &1"), b.TermAs[Real]("|x₀|"))),
							)
							vanishes := b.Have(
								"so the cutoff vanishes at x",
								"«cutoff»(K₀, x₀) = &0",
								By(far, cutoff),
							)
							bothBounded := b.Have(
								"f and its clipped copy are bounded by B at x",
								"|f₀(x₀)| ≤ B₀ ∧ |«clippedTest»(f₀, K₀, x₀)| ≤ B₀",
								By(bounded),
							)
							apart := b.Have(
								"so they are within 2B",
								"|f₀(x₀) - «clippedTest»(f₀, K₀, x₀)| ≤ &2 * B₀",
								ByArith(
									bothBounded,
									real_sgn_abs.AbsTriangleSub.At(
										b.TermAs[Real]("f₀(x₀)"), b.TermAs[Real]("«clippedTest»(f₀, K₀, x₀)"))),
							)
							b.Show(
								"and 2B is the envelope where the cutoff vanishes",
								ByArith(vanishes, apart),
							)
						})
				})

			cutoffUniform := ctx.Lemma("∀K:real. "+
				"    real_uniformly_continuous_on(𝕌, λx:real. «cutoff»(K, x)) ∧ "+
				"    «boundedBy»(λx:real. «cutoff»(K, x), &1)",
				func(a *Argument, K *Expr[Real]) {
					lipschitz := a.Have(
						"the cutoff moves no two points further apart",
						"∀x y:real. |«cutoff»(K₀, x) - «cutoff»(K₀, y)| ≤ |x - y|",
						Derive(func(b *Argument) {
							x := b.FixAs[Real]()
							y := b.FixAs[Real]()
							gap := b.Have(
								"the two arguments of the clip differ by |y| − |x|",
								"K₀ + &1 - |x₀| - (K₀ + &1 - |y₀|) = |y₀| - |x₀|",
								ByArith(Raw),
							)
							reverse := b.Have(
								"which the reverse triangle inequality bounds by |x − y|",
								"|K₀ + &1 - |x₀| - (K₀ + &1 - |y₀|)| ≤ |x₀ - y₀|",
								By(gap, real_sgn_abs.AbsReverseTriangle.At(y, x), real_sgn_abs.AbsSubComm.At(y, x)),
							)
							clipped := b.Have(
								"clipping to [0, 1] moves them no further apart",
								"|(λx:real. «cutoff»(K₀, x))(x₀) - (λx:real. «cutoff»(K₀, x))(y₀)| ≤ "+
									"|K₀ + &1 - |x₀| - (K₀ + &1 - |y₀|)|",
								By(
									real_sup_inf.ClampNonexpansive.At(
										b.TermAs[Real]("&0"),
										b.TermAs[Real]("&1"),
										b.TermAs[Real]("K₀ + &1 - |x₀|"),
										b.TermAs[Real]("K₀ + &1 - |y₀|"))),
							)
							b.Show(
								"so the cutoff values are within |x − y|",
								By(
									reverse,
									clipped,
									real_construction.LessEqTrans.At(
										b.TermAs[Real]("|(λx:real. «cutoff»(K₀, x))(x₀) - (λx:real. «cutoff»(K₀, x))(y₀)|"),
										b.TermAs[Real]("|K₀ + &1 - |x₀| - (K₀ + &1 - |y₀|)|"),
										b.TermAs[Real]("|x₀ - y₀|"))),
							)
						}),
					)
					uniform := a.Have(
						"so the cutoff is uniformly continuous",
						"real_uniformly_continuous_on(𝕌, λx:real. «cutoff»(K₀, x))",
						By(
							lipschitz,
							real_continuous.NonexpansiveUniformlyContinuous.At(
								a.TermAs[Fun[Real, Real]]("λx:real. «cutoff»(K₀, x)"))),
					)
					bounded := a.Have(
						"and bounded by 1",
						"«boundedBy»(λx:real. «cutoff»(K₀, x), &1)",
						Derive(func(b *Argument) {
							x := b.FixAs[Real]()
							inUnit := b.Have(
								"its value at x lies in [0, 1]",
								"&0 ≤ «cutoff»(K₀, x₀) ∧ «cutoff»(K₀, x₀) ≤ &1",
								By(At(cutoffProperties, K, x)),
							)
							b.Show(
								"so its absolute value is at most 1",
								By(inUnit, real_sgn_abs.AbsFixedIffNonneg.At(b.TermAs[Real]("«cutoff»(K₀, x₀)"))),
							)
						}),
					)
					a.Show(
						"the cutoff is uniformly continuous and bounded by 1",
						By(uniform, bounded),
					)
				})

			// Clipping f to the window ⟦−(K + 1), K + 1⟧ keeps its bound, and the clipped test is
			// uniformly continuous on the whole line: f is continuous on the window, and read through
			// the clamp to a closed interval it is continuous on, a function is uniformly continuous.
			clippedUniform := ctx.Lemma(Statement{
				Binders: "∀f:(real → real). ∀K B:real.",
				Hypotheses: []string{
					"real_continuous_on(𝕌, f)",
					"&0 ≤ K",
					"«boundedBy»(f, B)",
				},
				Conclusion: "real_uniformly_continuous_on(𝕌, λx:real. «clippedTest»(f, K, x)) ∧ " +
					"«boundedBy»(λx:real. «clippedTest»(f, K, x), B)",
			},
				func(a *Argument, f *Arrow[Real, Real], K, B *Expr[Real], continuous, nonneg, bounded Fact) {
					wide := a.Have(
						"the window ⟦−(K + 1), K + 1⟧ is not empty",
						"-(K₀ + &1) ≤ K₀ + &1",
						ByArith(Raw, nonneg),
					)
					inLine := a.Have(
						"the window is a part of the line",
						"«window»(K₀ + &1) ⊆ 𝕌",
						BySets(),
					)
					onWindow := a.Have(
						"so f is continuous on the window",
						"real_continuous_on(«window»(K₀ + &1), f₀)",
						By(
							continuous,
							inLine,
							real_continuous.ContinuousOnSubset.At(
								f, a.TermAs[Set[Real]]("𝕌"), a.TermAs[Set[Real]]("«window»(K₀ + &1)"))),
					)
					a.Show(
						"so f through the clamp to the window is uniformly continuous, and it keeps f's bound B",
						By(
							wide,
							onWindow,
							bounded,
							real_continuous.ClampedUniformlyContinuous.At(
								f, a.TermAs[Real]("-(K₀ + &1)"), a.TermAs[Real]("K₀ + &1"))),
					)
				})

			// f and its clipped copy differ by at most the tail envelope 2B(1 − cutoff), and all three
			// are integrable: so their integrals differ by at most 2B(1 − ∫ cutoff).
			tailIntegralError := ctx.Lemma(Statement{
				Binders: "∀μ:((real → bool) → extended_nonneg_real). ∀f:(real → real). ∀K B:real.",
				Hypotheses: []string{
					"«lineProbability»(μ)",
					"real_continuous_on(𝕌, f)",
					"&0 ≤ K",
					"&0 ≤ B",
					"«boundedBy»(f, B)",
				},
				Conclusion: "|«lineIntegral»(μ, f) - «lineIntegral»(μ, λx:real. «clippedTest»(f, K, x))| ≤ " +
					"&2 * B * (&1 - «lineIntegral»(μ, λx:real. «cutoff»(K, x)))",
			},
				func(a *Argument, μ *Arrow[Set[Real], ExtendedNonnegReal], f *Arrow[Real, Real], K, B *Expr[Real],
					probability, continuous, nonnegK, nonnegB, bounded Fact) {
					measure := a.Have(
						"a probability is a measure",
						"«lineMeasure»(μ₀)",
						By(
							probability,
							probability_space.ProbabilityOnDef.At(
								a.TermAs[Set[Real]]("𝕌"), a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"), μ)),
					)
					integrableF := a.Have(
						"f is integrable",
						"«lineIntegrable»(μ₀, f₀)",
						By(probability, continuous, bounded, At(continuousIntegrable, μ, f, B)),
					)
					clipped := a.Have(
						"the clipped test is uniformly continuous and bounded by B",
						"real_uniformly_continuous_on(𝕌, λx:real. «clippedTest»(f₀, K₀, x)) ∧ "+
							"«boundedBy»(λx:real. «clippedTest»(f₀, K₀, x), B₀)",
						By(continuous, nonnegK, bounded, At(clippedUniform, f, K, B)),
					)
					clippedContinuous := a.Have(
						"so it is continuous",
						"real_continuous_on(𝕌, λx:real. «clippedTest»(f₀, K₀, x))",
						By(
							clipped,
							real_continuous.UniformlyContinuousContinuous.At(
								a.TermAs[Fun[Real, Real]]("λx:real. «clippedTest»(f₀, K₀, x)"), a.TermAs[Set[Real]]("𝕌"))),
					)
					integrableClipped := a.Have(
						"and integrable",
						"«lineIntegrable»(μ₀, λx:real. «clippedTest»(f₀, K₀, x))",
						By(
							probability,
							clippedContinuous,
							clipped,
							At(continuousIntegrable, μ, a.TermAs[Fun[Real, Real]]("λx:real. «clippedTest»(f₀, K₀, x)"), B)),
					)
					cutoffFacts := a.Have(
						"the cutoff is uniformly continuous and bounded by 1",
						"real_uniformly_continuous_on(𝕌, λx:real. «cutoff»(K₀, x)) ∧ "+
							"«boundedBy»(λx:real. «cutoff»(K₀, x), &1)",
						By(At(cutoffUniform, K)),
					)
					cutoffContinuous := a.Have(
						"so it is continuous",
						"real_continuous_on(𝕌, λx:real. «cutoff»(K₀, x))",
						By(
							cutoffFacts,
							real_continuous.UniformlyContinuousContinuous.At(
								a.TermAs[Fun[Real, Real]]("λx:real. «cutoff»(K₀, x)"), a.TermAs[Set[Real]]("𝕌"))),
					)
					integrableCutoff := a.Have(
						"and integrable",
						"«lineIntegrable»(μ₀, λx:real. «cutoff»(K₀, x))",
						By(
							probability,
							cutoffContinuous,
							cutoffFacts,
							At(
								continuousIntegrable,
								μ,
								a.TermAs[Fun[Real, Real]]("λx:real. «cutoff»(K₀, x)"),
								a.TermAs[Real]("&1"))),
					)
					one := a.Have(
						"against a probability the constant 1 is integrable, with integral 1",
						"«lineIntegrable»(μ₀, λx:real. &1) ∧ «lineIntegral»(μ₀, λx:real. &1) = &1",
						By(
							probability,
							probability_space.ExpectationConstant.At(
								a.TermAs[Set[Real]]("𝕌"),
								a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"),
								μ,
								a.TermAs[Real]("&1")),
							probability_space.ExpectationDef.At(
								a.TermAs[Set[Real]]("𝕌"),
								a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"),
								μ,
								a.TermAs[Fun[Real, Real]]("λx:real. &1"))),
					)
					negatedCutoff := a.Have(
						"−cutoff is integrable",
						"«lineIntegrable»(μ₀, λx:real. -&1 * «cutoff»(K₀, x))",
						By(
							measure,
							integrableCutoff,
							measure_integral.IntegrableScale.At(
								a.TermAs[Set[Real]]("𝕌"),
								a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"),
								μ,
								a.TermAs[Fun[Real, Real]]("λx:real. «cutoff»(K₀, x)"),
								a.TermAs[Real]("-&1"))),
					)
					complementSum := a.Have(
						"so is 1 + (−cutoff)",
						"«lineIntegrable»(μ₀, λx:real. &1 + (λx:real. -&1 * «cutoff»(K₀, x))(x))",
						By(
							measure,
							one,
							negatedCutoff,
							measure_integral.IntegrableAdd.At(
								a.TermAs[Set[Real]]("𝕌"),
								a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"),
								μ,
								a.TermAs[Fun[Real, Real]]("λx:real. &1"),
								a.TermAs[Fun[Real, Real]]("λx:real. -&1 * «cutoff»(K₀, x)"))),
					)
					complementForm := a.Have(
						"1 − cutoff is 1 + (−cutoff)",
						"(λx:real. &1 - «cutoff»(K₀, x)) = λx:real. &1 + (λx:real. -&1 * «cutoff»(K₀, x))(x)",
						Funext(),
						Derive(func(b *Argument) {
							b.FixAs[Real]()
							b.Show(
								"1 − c = 1 + (−1)·c",
								ByArith(Raw),
							)
						}),
					)
					integrableComplement := a.Have(
						"so 1 − cutoff is integrable",
						"«lineIntegrable»(μ₀, λx:real. &1 - «cutoff»(K₀, x))",
						By(complementSum, complementForm),
					)
					integrableEnvelope := a.Have(
						"and so is the tail envelope 2B(1 − cutoff)",
						"«lineIntegrable»(μ₀, λx:real. «tailEnvelope»(B₀, K₀, x))",
						By(
							measure,
							integrableComplement,
							measure_integral.IntegrableScale.At(
								a.TermAs[Set[Real]]("𝕌"),
								a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"),
								μ,
								a.TermAs[Fun[Real, Real]]("λx:real. &1 - «cutoff»(K₀, x)"),
								a.TermAs[Real]("&2 * B₀"))),
					)
					complementIntegral := a.Have(
						"∫ (1 − cutoff) = 1 − ∫ cutoff",
						"«lineIntegral»(μ₀, λx:real. &1 - «cutoff»(K₀, x)) = "+
							"&1 - «lineIntegral»(μ₀, λx:real. «cutoff»(K₀, x))",
						By(
							measure,
							one,
							integrableCutoff,
							measure_integral.IntegralSub.At(
								a.TermAs[Set[Real]]("𝕌"),
								a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"),
								μ,
								a.TermAs[Fun[Real, Real]]("λx:real. &1"),
								a.TermAs[Fun[Real, Real]]("λx:real. «cutoff»(K₀, x)"))),
					)
					envelopeIntegral := a.Have(
						"∫ 2B(1 − cutoff) = 2B ∫ (1 − cutoff)",
						"«lineIntegral»(μ₀, λx:real. «tailEnvelope»(B₀, K₀, x)) = "+
							"&2 * B₀ * «lineIntegral»(μ₀, λx:real. &1 - «cutoff»(K₀, x))",
						By(
							measure,
							measure_integral.IntegralScale.At(
								a.TermAs[Set[Real]]("𝕌"),
								a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"),
								μ,
								a.TermAs[Fun[Real, Real]]("λx:real. &1 - «cutoff»(K₀, x)"),
								a.TermAs[Real]("&2 * B₀"))),
					)
					pointwise := a.Have(
						"pointwise f and its clipped copy differ by at most the tail envelope",
						"∀x:real. |f₀(x) - «clippedTest»(f₀, K₀, x)| ≤ «tailEnvelope»(B₀, K₀, x)",
						By(nonnegK, nonnegB, bounded, At(cutoffError, f, K, B)),
					)
					integralGap := a.Have(
						"so their integrals differ by at most the envelope's integral",
						"|«lineIntegral»(μ₀, f₀) - «lineIntegral»(μ₀, λx:real. «clippedTest»(f₀, K₀, x))| ≤ "+
							"«lineIntegral»(μ₀, λx:real. «tailEnvelope»(B₀, K₀, x))",
						By(
							measure,
							integrableF,
							integrableClipped,
							integrableEnvelope,
							pointwise,
							At(
								integralComparison,
								μ,
								f,
								a.TermAs[Fun[Real, Real]]("λx:real. «clippedTest»(f₀, K₀, x)"),
								a.TermAs[Fun[Real, Real]]("λx:real. «tailEnvelope»(B₀, K₀, x)"))),
					)
					a.Show(
						"which is 2B(1 − ∫ cutoff)",
						By(complementIntegral, envelopeIntegral, integralGap),
					)
				})

			windowAbsolute := ctx.Lemma("∀K:real. «window»(K) = {x:real | |x| ≤ K}",
				func(a *Argument, K *Expr[Real]) {
					a.Do(Funext())
					x := a.FixAs[Real]()
					a.Show(
						"x lies in ⟦−K, K⟧ exactly when |x| ≤ K",
						BySets(real_sgn_abs.AbsBounds.At(x, K)),
					)
				})

			growingWindows := ctx.Lemma("(∀n:num. «growingWindow»(n) ⊆ «growingWindow»(n + 1)) ∧ "+
				"⋃image(«growingWindow», 𝕌) = 𝕌",
				func(a *Argument) {
					a.Do(SplitConj(
						Case(
							"each window ⟦−n, n⟧ lies in the next",
							Derive(func(b *Argument) {
								n := b.FixAs[Nat]()
								successor := b.Have(
									"n + 1 as a real is n + 1",
									"&(n₀ + 1) = &n₀ + &1",
									By(Normalized, nat_arith.Add1.At(n), real_ring.OfNumSuc.At(n)),
								)
								widen := b.Have(
									"a point within n of 0 is within n + 1",
									"∀x:real. |x| ≤ &n₀ ⇒ |x| ≤ &(n₀ + 1)",
									Derive(func(c *Argument) {
										c.FixAs[Real]()
										within := c.Assume()
										c.Show(
											"since n ≤ n + 1",
											ByArith(Raw, within, successor),
										)
									}),
								)
								b.Show(
									"so ⟦−n, n⟧ ⊆ ⟦−(n + 1), n + 1⟧",
									BySets(
										widen,
										At(windowAbsolute, b.TermAs[Real]("&n₀")),
										At(windowAbsolute, b.TermAs[Real]("&(n₀ + 1)"))),
								)
							}),
						),
						Case(
							"and together the windows cover the line",
							Derive(func(b *Argument) {
								cover := b.Have(
									"every point lies in some window",
									"∀x:real. ∃m:num. m ∈ 𝕌 ∧ x ∈ «growingWindow»(m)",
									Derive(func(c *Argument) {
										x := c.FixAs[Real]()
										j, bounds := c.ObtainAs[Nat](
											"an index j with −j ≤ x ≤ j",
											"∃j:num. -&j ≤ x₀ ∧ x₀ ≤ &j",
											By(real_archimedean.ExistsNumBounds.At(x)),
										)
										c.Show(
											"x lies in the j-th window",
											Witness(j),
											Derive(func(d *Argument) {
												within := d.Have(
													"|x| ≤ j",
													"|x₀| ≤ &j₀",
													By(bounds, real_sgn_abs.AbsBounds.At(x, d.TermAs[Real]("&j₀"))),
												)
												d.Show(
													"so x ∈ ⟦−j, j⟧",
													BySets(within, At(windowAbsolute, d.TermAs[Real]("&j₀"))),
												)
											}),
										)
									}),
								)
								b.Show(
									"so their union is the line",
									BySets(cover),
								)
							}),
						),
					))
				})

			// The windows ⟦−n, n⟧ increase to the line, so their masses rise to the line's mass 1
			// (continuity of the measure from below): if none exceeded 1 − e, neither would 1.
			nearOneWindow := ctx.Lemma(Statement{
				Binders: "∀μ:(set(real) → extended_nonneg_real). ∀e:real.",
				Hypotheses: []string{
					"«lineProbability»(μ)",
					"&0 < e",
					"e < &1",
				},
				Conclusion: "∃n:num. &1 - e < extended_to_real(μ(«growingWindow»(n)))",
			},
				func(
					a *Argument,
					μ *Arrow[Set[Real], ExtendedNonnegReal],
					e *Expr[Real],
					probability, pos, belowOne Fact,
				) {
					measure := a.Have(
						"μ is a measure of mass 1 on the Borel sets",
						"«lineMeasure»(μ₀) ∧ μ₀(𝕌) = extended_of_real(&1)",
						By(
							probability,
							probability_space.ProbabilityOnDef.At(
								a.TermAs[Set[Real]]("𝕌"), a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"), μ)),
					)
					windowsBorel := a.Have(
						"each window is a Borel set",
						"∀n:num. «growingWindow»(n) ∈ borel_sets(real_topology)",
						Derive(func(b *Argument) {
							b.FixAs[Nat]()
							b.Show(
								"a closed interval is a Borel set",
								By(borel_function.ClosedIntervalBorel.At(b.TermAs[Real]("-&n₀"), b.TermAs[Real]("&n₀"))),
							)
						}),
					)
					windows := a.Have(
						"the windows increase and cover the line",
						"(∀n:num. «growingWindow»(n) ⊆ «growingWindow»(n + 1)) ∧ ⋃image(«growingWindow», 𝕌) = 𝕌",
						By(Normalized, growingWindows),
					)
					limit := a.Have(
						"so the masses of the windows rise to the mass of the line",
						"μ₀(𝕌) = extended_sup(image(λi:num. μ₀(«growingWindow»(i)), 𝕌))",
						By(
							measure,
							windowsBorel,
							windows,
							measure_space.MeasureContinuousIncreasing.At(
								a.TermAs[Set[Real]]("𝕌"),
								a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"),
								μ,
								a.TermAs[Fun2[Nat, Real, Bool]]("«growingWindow»"))),
					)
					marginNonneg := a.Have(
						"1 − e is nonnegative",
						"&0 ≤ &1 - e₀",
						ByArith(Raw, belowOne),
					)
					marginReal := a.Have(
						"so 1 − e read as an extended real and back is 1 − e",
						"extended_to_real(extended_of_real(&1 - e₀)) = &1 - e₀",
						By(marginNonneg, extended_nonneg_real.ToRealOfReal.At(a.TermAs[Real]("&1 - e₀"))),
					)
					none := a.SupposeNot()
					capped := a.Have(
						"then every window has mass at most 1 − e",
						"∀n:num. μ₀(«growingWindow»(n)) ≤ extended_of_real(&1 - e₀)",
						Derive(func(b *Argument) {
							b.FixAs[Nat]()
							inLine := b.Have(
								"the window lies in the line",
								"«growingWindow»(n₀) ⊆ 𝕌",
								BySets(),
							)
							belowLine := b.Have(
								"so its mass is at most the line's",
								"μ₀(«growingWindow»(n₀)) ≤ μ₀(𝕌)",
								By(
									measure,
									windowsBorel,
									lineMeasurableCarrier,
									inLine,
									measure_space.MeasureMono.At(
										b.TermAs[Set[Real]]("𝕌"),
										b.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"),
										μ,
										b.TermAs[Set[Real]]("«growingWindow»(n₀)"),
										b.TermAs[Set[Real]]("𝕌"))),
							)
							finite := b.Have(
								"and finite",
								"μ₀(«growingWindow»(n₀)) ≠ extended_infinity",
								By(
									measure,
									belowLine,
									extended_nonneg_real.ExtendedLeDef.At(
										b.TermAs[ExtendedNonnegReal]("μ₀(«growingWindow»(n₀))"), b.TermAs[ExtendedNonnegReal]("μ₀(𝕌)")),
									extended_nonneg_real.OfRealNotInfinity.At(b.TermAs[Real]("&1"))),
							)
							realBound := b.Have(
								"read as a real it is at most 1 − e, by the supposition",
								"extended_to_real(μ₀(«growingWindow»(n₀))) ≤ &1 - e₀",
								By(
									none,
									real_order_ring.NotLessThan.At(
										b.TermAs[Real]("&1 - e₀"), b.TermAs[Real]("extended_to_real(μ₀(«growingWindow»(n₀)))"))),
							)
							b.Show(
								"so it is at most 1 − e as an extended real",
								By(
									finite,
									realBound,
									marginReal,
									extended_nonneg_real.ExtendedLeDef.At(
										b.TermAs[ExtendedNonnegReal]("μ₀(«growingWindow»(n₀))"),
										b.TermAs[ExtendedNonnegReal]("extended_of_real(&1 - e₀)"))),
							)
						}),
					)
					supremumCapped := a.Have(
						"so is the supremum of their masses",
						"extended_sup(image(λi:num. μ₀(«growingWindow»(i)), 𝕌)) ≤ extended_of_real(&1 - e₀)",
						By(
							capped,
							extended_nonneg_real.SupSequenceLeast.At(
								a.TermAs[Fun[Nat, ExtendedNonnegReal]]("λi:num. μ₀(«growingWindow»(i))"),
								a.TermAs[ExtendedNonnegReal]("extended_of_real(&1 - e₀)"))),
					)
					oneCapped := a.Have(
						"so the line's mass 1 is at most 1 − e",
						"&1 ≤ extended_of_real(&1 - e₀)",
						By(measure, limit, supremumCapped),
					)
					realOneCapped := a.Have(
						"and 1 ≤ 1 − e as reals",
						"&1 ≤ &1 - e₀",
						By(
							marginNonneg,
							oneCapped,
							extended_nonneg_real.OfRealLe.At(a.TermAs[Real]("&1"), a.TermAs[Real]("&1 - e₀"))),
					)
					a.Show(
						"against e > 0",
						ByArith(Raw, pos, realOneCapped),
					)
				})

			// A window ⟦−n, n⟧ of mass above 1 − e lies under the cutoff at n, which is integrable:
			// so the cutoff's integral is above 1 − e.
			nearOneTent := ctx.Lemma(Statement{
				Binders: "∀μ:((real → bool) → extended_nonneg_real). ∀e:real.",
				Hypotheses: []string{
					"«lineProbability»(μ)",
					"&0 < e",
					"e < &1",
				},
				Conclusion: "∃K:real. &0 ≤ K ∧ &1 - e < «lineIntegral»(μ, λx:real. «cutoff»(K, x))",
			},
				func(
					a *Argument,
					μ *Arrow[Set[Real], ExtendedNonnegReal],
					e *Expr[Real],
					probability, pos, belowOne Fact,
				) {
					line := a.TermAs[Set[Real]]("𝕌")
					borelSets := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
					n, window := a.ObtainAs[Nat](
						"some window ⟦−n, n⟧ has mass above 1 − e",
						"∃n:num. &1 - e₀ < extended_to_real(μ₀(«growingWindow»(n)))",
						By(probability, pos, belowOne, At(nearOneWindow, μ, e)),
					)
					windowBorel := a.Have(
						"the window is a Borel set",
						"«growingWindow»(n₀) ∈ borel_sets(real_topology)",
						By(borel_function.ClosedIntervalBorel.At(a.TermAs[Real]("-&n₀"), a.TermAs[Real]("&n₀"))),
					)
					windowIndicator := a.TermAs[Fun[Real, Real]]("λx:real. «indicator»(«growingWindow»(n₀), &1, x)")
					indicator := a.Have(
						"so its indicator is integrable, with integral the window's mass",
						"«lineIntegrable»(μ₀, λx:real. «indicator»(«growingWindow»(n₀), &1, x)) ∧ "+
							"«lineIntegral»(μ₀, λx:real. «indicator»(«growingWindow»(n₀), &1, x)) = "+
							"extended_to_real(μ₀(«growingWindow»(n₀)))",
						ByArith(
							probability,
							windowBorel,
							probability_space.ExpectationIndicator.At(
								line, borelSets, μ, a.TermAs[Set[Real]]("«growingWindow»(n₀)"), a.TermAs[Real]("&1")),
							probability_space.ExpectationDef.At(line, borelSets, μ, windowIndicator)),
					)
					cutoffFacts := a.Have(
						"the cutoff at n is uniformly continuous and bounded by 1",
						"real_uniformly_continuous_on(𝕌, λx:real. «cutoff»(&n₀, x)) ∧ "+
							"«boundedBy»(λx:real. «cutoff»(&n₀, x), &1)",
						By(At(cutoffUniform, a.TermAs[Real]("&n₀"))),
					)
					cutoffContinuous := a.Have(
						"so it is continuous",
						"real_continuous_on(𝕌, λx:real. «cutoff»(&n₀, x))",
						By(
							cutoffFacts,
							real_continuous.UniformlyContinuousContinuous.At(
								a.TermAs[Fun[Real, Real]]("λx:real. «cutoff»(&n₀, x)"), a.TermAs[Set[Real]]("𝕌"))),
					)
					cutoffIntegrable := a.Have(
						"and integrable",
						"«lineIntegrable»(μ₀, λx:real. «cutoff»(&n₀, x))",
						By(
							probability,
							cutoffContinuous,
							cutoffFacts,
							At(
								continuousIntegrable,
								μ,
								a.TermAs[Fun[Real, Real]]("λx:real. «cutoff»(&n₀, x)"),
								a.TermAs[Real]("&1"))),
					)
					dominates := a.Have(
						"the cutoff at n lies above the indicator of ⟦−n, n⟧",
						"∀x:real. x ∈ 𝕌 ⇒ «indicator»(«growingWindow»(n₀), &1, x) ≤ «cutoff»(&n₀, x)",
						Derive(func(b *Argument) {
							x := b.FixAs[Real]()
							b.Assume()
							membership := b.Have(
								"x lies in ⟦−n, n⟧ exactly when |x| ≤ n",
								"x₀ ∈ «growingWindow»(n₀) ⇔ |x₀| ≤ &n₀",
								BySets(At(windowAbsolute, b.TermAs[Real]("&n₀"))),
							)
							cutoffAt := b.Have(
								"the cutoff is nonnegative, and 1 where |x| ≤ n",
								"&0 ≤ «cutoff»(&n₀, x₀) ∧ (|x₀| ≤ &n₀ ⇒ «cutoff»(&n₀, x₀) = &1)",
								By(At(cutoffProperties, b.TermAs[Real]("&n₀"), x)),
							)
							b.Show(
								"so it lies above the indicator at x",
								ByArith(membership, cutoffAt),
							)
						}),
					)
					integralBelow := a.Have(
						"so the indicator's integral is at most the cutoff's",
						"«lineIntegral»(μ₀, λx:real. «indicator»(«growingWindow»(n₀), &1, x)) ≤ "+
							"«lineIntegral»(μ₀, λx:real. «cutoff»(&n₀, x))",
						By(
							dominates,
							indicator,
							cutoffIntegrable,
							measure_integral.IntegralMono.At(
								line,
								borelSets,
								μ,
								windowIndicator,
								a.TermAs[Fun[Real, Real]]("λx:real. «cutoff»(&n₀, x)"))),
					)
					a.Show(
						"so the cutoff at K = n has integral above 1 − e",
						Witness(a.TermAs[Real]("&n₀")),
						ByArith(Raw, window, integralBelow, indicator, real_order_ring.NumNonneg.At(n)),
					)
				})

			// For ε > 0 take the tolerance δ = min(1/2, ε/(16(B + 1))) and a cutoff at K whose
			// ρ-integral is above 1 − δ. The cutoff and f clipped to the window are uniformly continuous
			// and bounded, so their integrals converge. Past both indices the ν(n)-integral of the
			// cutoff is above 1 − 2δ, and the three gaps — f to its clipped copy under ν(n), at most
			// 4Bδ; the clipped copy from ν(n) to ρ, below ε/2; back to f under ρ, at most 2Bδ — add up
			// to less than ε.
			continuousTestConvergence := ctx.Lemma(Statement{
				Binders: "∀ν:(num → (real → bool) → extended_nonneg_real). " +
					"∀ρ:((real → bool) → extended_nonneg_real). " +
					"∀f:(real → real). " +
					"∀B:real.",
				Hypotheses: []string{
					"∀n:num. «lineProbability»(ν(n))",
					"«lineProbability»(ρ)",
					"«smoothConverges»(ν, ρ)",
					"real_continuous_on(𝕌, f)",
					"«boundedBy»(f, B)",
				},
				Conclusion: "«convergesFor»(ν, ρ, f)",
			},
				func(
					a *Argument,
					ν *Arrow[Nat, Fun[Set[Real], ExtendedNonnegReal]],
					ρ *Arrow[Set[Real], ExtendedNonnegReal],
					f *Arrow[Real, Real],
					B *Expr[Real],
					probabilities, probability, smoothTests, continuous, bounded Fact,
				) {
					atZero := a.Have(
						"f is bounded by B at 0",
						"|f₀(&0)| ≤ B₀",
						By(bounded),
					)
					boundNonneg := a.Have(
						"so B is nonnegative",
						"&0 ≤ B₀",
						ByArith(Raw, atZero, real_sgn_abs.AbsNonneg.At(a.TermAs[Real]("f₀(&0)"))),
					)
					scalePos := a.Have(
						"16(B + 1) is positive",
						"&0 < &16 * (B₀ + &1)",
						ByArith(Raw, boundNonneg),
					)
					eventually := a.Have(
						"for every ε > 0, from some index on the integrals of f are within ε of their limit",
						Statement{
							Binders: "∀ε:real.",
							Hypotheses: []string{
								"&0 < ε",
							},
							Conclusion: "∃N:num. ∀n:num. N ≤ n ⇒ |«lineIntegral»(ν₀(n), f₀) - «lineIntegral»(ρ₀, f₀)| < ε",
						},
						Derive(func(b *Argument) {
							ε := b.FixAs[Real]()
							pos := b.Assume()
							ratio := b.Have(
								"ε/(16(B + 1)) is positive",
								"&0 < ε₀ / (&16 * (B₀ + &1))",
								By(pos, scalePos, real_order_field.DivPos.At(ε, b.TermAs[Real]("&16 * (B₀ + &1)"))),
							)
							tolerance := b.Have(
								"the tolerance δ = min(1/2, ε/(16(B + 1))) is positive, below 1 and at most ε/(16(B + 1))",
								"&0 < min(&1 / &2, ε₀ / (&16 * (B₀ + &1))) ∧ "+
									"min(&1 / &2, ε₀ / (&16 * (B₀ + &1))) < &1 ∧ "+
									"min(&1 / &2, ε₀ / (&16 * (B₀ + &1))) ≤ ε₀ / (&16 * (B₀ + &1))",
								ByArith(
									ratio,
									real_sup_inf.RealMinDef.At(b.TermAs[Real]("&1 / &2"), b.TermAs[Real]("ε₀ / (&16 * (B₀ + &1))"))),
							)
							scaled := b.Have(
								"so 16(B + 1)·δ ≤ ε",
								"min(&1 / &2, ε₀ / (&16 * (B₀ + &1))) * (&16 * (B₀ + &1)) ≤ ε₀",
								By(
									tolerance,
									scalePos,
									real_order_field.LessEqDivMulLeft.At(
										b.TermAs[Real]("min(&1 / &2, ε₀ / (&16 * (B₀ + &1)))"), ε, b.TermAs[Real]("&16 * (B₀ + &1)"))),
							)
							budget := b.Have(
								"and the three gaps 4Bδ, ε/2 and 2Bδ add up to at most ε",
								"&4 * B₀ * min(&1 / &2, ε₀ / (&16 * (B₀ + &1))) + "+
									"ε₀ / &2 + "+
									"&2 * B₀ * min(&1 / &2, ε₀ / (&16 * (B₀ + &1))) ≤ "+
									"ε₀",
								ByArith(Raw, tolerance, boundNonneg, scaled),
							)
							K, heavy := b.ObtainAs[Real](
								"a cutoff at some K ≥ 0 has ρ-integral above 1 − δ",
								"∃K:real. "+
									"    &0 ≤ K ∧ "+
									"    &1 - min(&1 / &2, ε₀ / (&16 * (B₀ + &1))) < «lineIntegral»(ρ₀, λx:real. «cutoff»(K, x))",
								By(
									probability,
									tolerance,
									At(nearOneTent, ρ, b.TermAs[Real]("min(&1 / &2, ε₀ / (&16 * (B₀ + &1)))"))),
							)
							cutoffFacts := b.Have(
								"the cutoff at K is uniformly continuous and bounded by 1",
								"real_uniformly_continuous_on(𝕌, λx:real. «cutoff»(K₀, x)) ∧ "+
									"«boundedBy»(λx:real. «cutoff»(K₀, x), &1)",
								By(At(cutoffUniform, K)),
							)
							clippedFacts := b.Have(
								"f clipped to the window ⟦−(K + 1), K + 1⟧ is uniformly continuous and bounded by B",
								"real_uniformly_continuous_on(𝕌, λx:real. «clippedTest»(f₀, K₀, x)) ∧ "+
									"«boundedBy»(λx:real. «clippedTest»(f₀, K₀, x), B₀)",
								By(continuous, heavy, bounded, At(clippedUniform, f, K, B)),
							)
							cutoffConverges := b.Have(
								"so the cutoff's integrals converge",
								"«convergesFor»(ν₀, ρ₀, λx:real. «cutoff»(K₀, x))",
								By(
									probabilities,
									probability,
									smoothTests,
									cutoffFacts,
									At(
										uniformTestConvergence,
										ν,
										ρ,
										b.TermAs[Fun[Real, Real]]("λx:real. «cutoff»(K₀, x)"),
										b.TermAs[Real]("&1"))),
							)
							clippedConverges := b.Have(
								"and so do the clipped test's",
								"«convergesFor»(ν₀, ρ₀, λx:real. «clippedTest»(f₀, K₀, x))",
								By(
									probabilities,
									probability,
									smoothTests,
									clippedFacts,
									At(
										uniformTestConvergence, ν, ρ, b.TermAs[Fun[Real, Real]]("λx:real. «clippedTest»(f₀, K₀, x)"), B)),
							)
							cutoffIndex := b.Have(
								"from some index on, the cutoff's integrals under ν(n) are within δ of its integral under ρ",
								"∃p:num. ∀n:num. "+
									"    p ≤ n ⇒ "+
									"    |«lineIntegral»(ν₀(n), λx:real. «cutoff»(K₀, x)) - "+
									"    «lineIntegral»(ρ₀, λx:real. «cutoff»(K₀, x))| < "+
									"    min(&1 / &2, ε₀ / (&16 * (B₀ + &1)))",
								By(
									cutoffConverges,
									tolerance,
									real_sequences.RealConvergesToDef.At(
										b.TermAs[Fun[Nat, Real]]("λn:num. «lineIntegral»(ν₀(n), λx:real. «cutoff»(K₀, x))"),
										b.TermAs[Real]("«lineIntegral»(ρ₀, λx:real. «cutoff»(K₀, x))"))),
							)
							half := b.Have(
								"ε/2 is positive",
								"&0 < ε₀ / &2",
								ByArith(Raw, pos),
							)
							clippedIndex := b.Have(
								"from some index on, the clipped test's integrals "+
									"under ν(n) are within ε/2 of its integral under ρ",
								"∃q:num. ∀n:num. "+
									"    q ≤ n ⇒ "+
									"    |«lineIntegral»(ν₀(n), λx:real. «clippedTest»(f₀, K₀, x)) - "+
									"    «lineIntegral»(ρ₀, λx:real. «clippedTest»(f₀, K₀, x))| < "+
									"    ε₀ / &2",
								By(
									clippedConverges,
									half,
									real_sequences.RealConvergesToDef.At(
										b.TermAs[Fun[Nat, Real]]("λn:num. «lineIntegral»(ν₀(n), λx:real. «clippedTest»(f₀, K₀, x))"),
										b.TermAs[Real]("«lineIntegral»(ρ₀, λx:real. «clippedTest»(f₀, K₀, x))"))),
							)
							_, cutoffTail := b.UnpackAs[Nat](cutoffIndex)
							_, clippedTail := b.UnpackAs[Nat](clippedIndex)
							b.Show(
								"past both indices, the three gaps add up to less than ε",
								Witness(b.TermAs[Nat]("p₀ + q₀")),
								Derive(func(c *Argument) {
									c.FixAs[Nat]()
									late := c.Assume()
									pastBoth := c.Have(
										"n is past both indices",
										"p₀ ≤ n₀ ∧ q₀ ≤ n₀",
										ByArith(Raw, late),
									)
									cutoffGap := c.Have(
										"the cutoff's integrals under ν(n) and ρ are within δ",
										"|«lineIntegral»(ν₀(n₀), λx:real. «cutoff»(K₀, x)) - "+
											"«lineIntegral»(ρ₀, λx:real. «cutoff»(K₀, x))| < "+
											"min(&1 / &2, ε₀ / (&16 * (B₀ + &1)))",
										By(pastBoth, cutoffTail),
									)
									clippedGap := c.Have(
										"the clipped test's within ε/2",
										"|«lineIntegral»(ν₀(n₀), λx:real. «clippedTest»(f₀, K₀, x)) - "+
											"«lineIntegral»(ρ₀, λx:real. «clippedTest»(f₀, K₀, x))| < "+
											"ε₀ / &2",
										By(pastBoth, clippedTail),
									)
									cutoffAbove := c.Have(
										"so the cutoff's ν(n)-integral is above its ρ-integral less δ",
										"«lineIntegral»(ρ₀, λx:real. «cutoff»(K₀, x)) - min(&1 / &2, ε₀ / (&16 * (B₀ + &1))) < "+
											"«lineIntegral»(ν₀(n₀), λx:real. «cutoff»(K₀, x))",
										By(
											cutoffGap,
											real_sgn_abs.AbsBetween.At(
												c.TermAs[Real]("«lineIntegral»(ρ₀, λx:real. «cutoff»(K₀, x))"),
												c.TermAs[Real]("«lineIntegral»(ν₀(n₀), λx:real. «cutoff»(K₀, x))"),
												c.TermAs[Real]("min(&1 / &2, ε₀ / (&16 * (B₀ + &1)))"))),
									)
									nuTail := c.Have(
										"so 1 less the cutoff's ν(n)-integral is at most 2δ",
										"&1 - «lineIntegral»(ν₀(n₀), λx:real. «cutoff»(K₀, x)) ≤ &2 * min(&1 / &2, ε₀ / (&16 * (B₀ + &1)))",
										ByArith(Raw, cutoffAbove, heavy),
									)
									rhoTail := c.Have(
										"and 1 less its ρ-integral is at most δ",
										"&1 - «lineIntegral»(ρ₀, λx:real. «cutoff»(K₀, x)) ≤ min(&1 / &2, ε₀ / (&16 * (B₀ + &1)))",
										ByArith(Raw, heavy),
									)
									doubleBound := c.Have(
										"2B is nonnegative",
										"&0 ≤ &2 * B₀",
										ByArith(Raw, boundNonneg),
									)
									nuClip := c.Have(
										"under ν(n), clipping moves the integral of f by at most 2B(1 − ∫ cutoff)",
										"|«lineIntegral»(ν₀(n₀), f₀) - «lineIntegral»(ν₀(n₀), λx:real. «clippedTest»(f₀, K₀, x))| ≤ "+
											"&2 * B₀ * (&1 - «lineIntegral»(ν₀(n₀), λx:real. «cutoff»(K₀, x)))",
										By(
											probabilities,
											continuous,
											bounded,
											heavy,
											boundNonneg,
											At(tailIntegralError, c.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("ν₀(n₀)"), f, K, B)),
									)
									nuClipScaled := c.Have(
										"and 2B(1 − ∫ cutoff) ≤ 2B·2δ there",
										"&2 * B₀ * (&1 - «lineIntegral»(ν₀(n₀), λx:real. «cutoff»(K₀, x))) ≤ "+
											"&2 * B₀ * (&2 * min(&1 / &2, ε₀ / (&16 * (B₀ + &1))))",
										By(
											doubleBound,
											nuTail,
											real_order_ring.LessEqMulLeft.At(
												c.TermAs[Real]("&2 * B₀"),
												c.TermAs[Real]("&1 - «lineIntegral»(ν₀(n₀), λx:real. «cutoff»(K₀, x))"),
												c.TermAs[Real]("&2 * min(&1 / &2, ε₀ / (&16 * (B₀ + &1)))"))),
									)
									nuClipBound := c.Have(
										"so the first gap is at most 4Bδ",
										"|«lineIntegral»(ν₀(n₀), f₀) - «lineIntegral»(ν₀(n₀), λx:real. «clippedTest»(f₀, K₀, x))| ≤ "+
											"&4 * B₀ * min(&1 / &2, ε₀ / (&16 * (B₀ + &1)))",
										ByArith(Raw, nuClip, nuClipScaled),
									)
									rhoClip := c.Have(
										"under ρ, clipping moves it by at most 2B(1 − ∫ cutoff)",
										"|«lineIntegral»(ρ₀, f₀) - «lineIntegral»(ρ₀, λx:real. «clippedTest»(f₀, K₀, x))| ≤ "+
											"&2 * B₀ * (&1 - «lineIntegral»(ρ₀, λx:real. «cutoff»(K₀, x)))",
										By(probability, continuous, bounded, heavy, boundNonneg, At(tailIntegralError, ρ, f, K, B)),
									)
									rhoClipScaled := c.Have(
										"and 2B(1 − ∫ cutoff) ≤ 2Bδ there",
										"&2 * B₀ * (&1 - «lineIntegral»(ρ₀, λx:real. «cutoff»(K₀, x))) ≤ "+
											"&2 * B₀ * min(&1 / &2, ε₀ / (&16 * (B₀ + &1)))",
										By(
											doubleBound,
											rhoTail,
											real_order_ring.LessEqMulLeft.At(
												c.TermAs[Real]("&2 * B₀"),
												c.TermAs[Real]("&1 - «lineIntegral»(ρ₀, λx:real. «cutoff»(K₀, x))"),
												c.TermAs[Real]("min(&1 / &2, ε₀ / (&16 * (B₀ + &1)))"))),
									)
									rhoClipBound := c.Have(
										"so the last gap, from the clipped copy back to f, is at most 2Bδ",
										"|«lineIntegral»(ρ₀, λx:real. «clippedTest»(f₀, K₀, x)) - «lineIntegral»(ρ₀, f₀)| ≤ "+
											"&2 * B₀ * min(&1 / &2, ε₀ / (&16 * (B₀ + &1)))",
										ByArith(
											rhoClip,
											rhoClipScaled,
											real_sgn_abs.AbsSubComm.At(
												c.TermAs[Real]("«lineIntegral»(ρ₀, λx:real. «clippedTest»(f₀, K₀, x))"),
												c.TermAs[Real]("«lineIntegral»(ρ₀, f₀)"))),
									)
									total := c.Have(
										"so f's integrals under ν(n) and ρ differ by less than the sum of the three gaps",
										"|«lineIntegral»(ν₀(n₀), f₀) - «lineIntegral»(ρ₀, f₀)| < "+
											"&4 * B₀ * min(&1 / &2, ε₀ / (&16 * (B₀ + &1))) + "+
											"ε₀ / &2 + "+
											"&2 * B₀ * min(&1 / &2, ε₀ / (&16 * (B₀ + &1)))",
										By(
											nuClipBound,
											clippedGap,
											rhoClipBound,
											At(
												threeTermError,
												c.TermAs[Real]("«lineIntegral»(ν₀(n₀), f₀)"),
												c.TermAs[Real]("«lineIntegral»(ν₀(n₀), λx:real. «clippedTest»(f₀, K₀, x))"),
												c.TermAs[Real]("«lineIntegral»(ρ₀, λx:real. «clippedTest»(f₀, K₀, x))"),
												c.TermAs[Real]("«lineIntegral»(ρ₀, f₀)"),
												c.TermAs[Real]("&4 * B₀ * min(&1 / &2, ε₀ / (&16 * (B₀ + &1)))"),
												c.TermAs[Real]("ε₀ / &2"),
												c.TermAs[Real]("&2 * B₀ * min(&1 / &2, ε₀ / (&16 * (B₀ + &1)))"))),
									)
									c.Show(
										"which the budget keeps below ε",
										ByArith(Raw, total, budget),
									)
								}),
							)
						}),
					)
					a.Show(
						"so the integrals of f converge to the one under ρ",
						By(
							eventually,
							real_sequences.RealConvergesToDef.At(
								a.TermAs[Fun[Nat, Real]]("λn:num. «lineIntegral»(ν₀(n), f₀)"),
								a.TermAs[Real]("«lineIntegral»(ρ₀, f₀)"))),
					)
				})

			// The constant 1 is the bottom of a bounded tower, so its integrals converge: under each
			// ν(n) they are 1, under ρ the mass of the line.
			probabilityMass := ctx.Lemma(Statement{
				Binders: "∀ν:(num → (real → bool) → extended_nonneg_real). " +
					"∀ρ:(set(real) → extended_nonneg_real).",
				Hypotheses: []string{
					"∀n:num. «lineProbability»(ν(n))",
					"«lineMeasure»(ρ)",
					"«smoothConverges»(ν, ρ)",
				},
				Conclusion: "ρ(𝕌) = &1",
			},
				func(
					a *Argument,
					ν *Arrow[Nat, Fun[Set[Real], ExtendedNonnegReal]],
					ρ *Arrow[Set[Real], ExtendedNonnegReal],
					probabilities, measure, smoothTests Fact,
				) {
					oneTower := a.Have(
						"the constant 1 is the bottom of a tower of three bounded derivatives",
						"(∀k:num. ∀y:real. "+
							"    k ≤ 2 ⇒ real_derivative_at(λx:real. COND(k = 0, &1, &0), y, COND(k + 1 = 0, &1, &0))) ∧ "+
							"(∃B:real. ∀k:num. ∀y:real. k ≤ 3 ⇒ |COND(k = 0, &1, &0)| ≤ B)",
						By(At(constantTower, a.TermAs[Real]("&1"))),
					)
					bottom := a.Have(
						"its bottom is the constant 1",
						"(λx:real. COND(0 = 0, &1, &0)) = λx:real. &1",
						ByArith(Raw),
					)
					towerConverges := a.Have(
						"so its integrals converge",
						"«convergesFor»(ν₀, ρ₀, λx:real. COND(0 = 0, &1, &0))",
						By(
							smoothTests.At(a.TermAs[Fun2[Nat, Real, Real]]("λk:num. λx:real. COND(k = 0, &1, &0)")),
							oneTower),
					)
					oneConverges := a.Have(
						"that is, the integrals of 1 converge",
						"«convergesFor»(ν₀, ρ₀, λx:real. &1)",
						By(towerConverges, bottom),
					)
					ones := a.Have(
						"under each ν(n), a probability, 1 integrates to 1",
						"(λn:num. «lineIntegral»(ν₀(n), λx:real. &1)) = λn:num. &1",
						Funext(),
						Derive(func(b *Argument) {
							b.FixAs[Nat]()
							b.Show(
								"by the expectation of a constant",
								By(
									probabilities,
									probability_space.ExpectationConstant.At(
										b.TermAs[Set[Real]]("𝕌"),
										b.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"),
										b.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("ν₀(n₀)"),
										b.TermAs[Real]("&1")),
									probability_space.ExpectationDef.At(
										b.TermAs[Set[Real]]("𝕌"),
										b.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"),
										b.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("ν₀(n₀)"),
										b.TermAs[Fun[Real, Real]]("λx:real. &1"))),
							)
						}),
					)
					onesConverge := a.Have(
						"so that sequence tends to 1",
						"(λn:num. «lineIntegral»(ν₀(n), λx:real. &1)) ⟶ &1",
						By(ones, real_sequences.LimitConst.At(a.TermAs[Real]("&1"))),
					)
					limitOne := a.Have(
						"limits are unique, so 1 integrates to 1 under ρ",
						"«lineIntegral»(ρ₀, λx:real. &1) = &1",
						By(
							oneConverges,
							onesConverge,
							real_sequences.LimitUnique.At(
								a.TermAs[Fun[Nat, Real]]("λn:num. «lineIntegral»(ν₀(n), λx:real. &1)"),
								a.TermAs[Real]("«lineIntegral»(ρ₀, λx:real. &1)"),
								a.TermAs[Real]("&1"))),
					)
					realMass := a.Have(
						"and that integral is the mass of the line, as a real",
						"extended_to_real(ρ₀(𝕌)) = &1",
						By(measure, limitOne, At(constantOneIntegral, ρ)),
					)
					oneNonzero := a.Have(
						"1 is not 0",
						"&1 ≠ &0",
						ByArith(Raw),
					)
					finite := a.Have(
						"so the mass of the line is finite",
						"ρ₀(𝕌) ≠ extended_infinity",
						By(realMass, oneNonzero, extended_nonneg_real.ToRealInfinity),
					)
					a.Show(
						"and it is 1",
						By(
							Normalized,
							realMass,
							finite,
							extended_nonneg_real.OfRealToReal.At(a.TermAs[ExtendedNonnegReal]("ρ₀(𝕌)"))),
					)
				})

			// The constant test makes ρ a probability; a bounded continuous test then converges by
			// continuousTestConvergence, which is what weak convergence asks.
			return ctx.Theorem(headline,
				func(
					a *Argument,
					ν *Arrow[Nat, Fun[Set[Real], ExtendedNonnegReal]],
					ρ *Arrow[Set[Real], ExtendedNonnegReal],
					probabilities, measure, smoothTests Fact,
				) {
					smooth := a.Unfolded(smoothTests, probability_space.ExpectationDef)
					unitMass := a.Have(
						"ρ has mass 1",
						"ρ₀(𝕌) = extended_of_real(&1)",
						By(probabilities, measure, smooth, At(probabilityMass, ν, ρ)),
					)
					a.Do(
						Unfold(WeaklyConvergesDef),
						SplitConjAll(
							Case(
								"the ν(n) are probabilities on the Borel sets of the line",
								By(probabilities, real_topology.RealSpace),
							),
							Case(
								"ρ, a measure of mass 1, is a probability there",
								By(
									measure,
									unitMass,
									real_topology.RealSpace,
									probability_space.ProbabilityOnDef.At(
										a.TermAs[Set[Real]]("𝕌"), a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"), ρ)),
							),
							Case(
								"and the integrals of every bounded continuous test converge",
								Derive(func(b *Argument) {
									f := b.FixAs[Fun[Real, Real]]()
									test := b.Assume()
									continuous := b.Have(
										"a continuous map of the line is continuous on the line",
										"real_continuous_on(𝕌, f₀)",
										By(test, real_continuous.ContinuousOnUnivIffMap.At(f)),
									)
									B, bounded := b.ObtainAs[Real](
										"f is bounded by some B",
										"∃B:real. «boundedBy»(f₀, B)",
										By(test, real_topology.RealSpace, set_basic.InUniv.Inst[Real]()),
									)
									converges := b.Have(
										"so its integrals converge",
										"«convergesFor»(ν₀, ρ₀, f₀)",
										By(
											measure,
											unitMass,
											smooth,
											probabilities,
											continuous,
											bounded,
											probability_space.ProbabilityOnDef.At(
												b.TermAs[Set[Real]]("𝕌"), b.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"), ρ),
											At(continuousTestConvergence, ν, ρ, f, B)),
									)
									b.Show(
										"under ν(n) to the one under ρ",
										By(converges, real_topology.RealSpace),
									)
								}),
							),
						),
					)
				})
		}),
})}
