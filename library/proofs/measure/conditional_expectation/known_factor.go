// known_factor.go — a known factor passes through conditional expectation, in
// three steps: a dominated almost-everywhere limit of related pairs is
// related; a G-measurable factor with finitely many values is a finite sum of
// cuts to conditioning events; and an almost-everywhere bounded G-measurable
// factor is a dominated limit of simple ones, taken on its two parts.

package conditional_expectation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/measure/event_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_simple"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// CondExpDominatedLimit — conditional expectations pass to dominated almost-everywhere limits:
// both limits are integrable, and their event integrals are limits of the same sequence.
var CondExpDominatedLimit = condExpDominatedLimitThm{family.Add(registry.ProofEntry{
	Name: "CondExpDominatedLimit",
	Key:  "prop_72643f6f6e009c8",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀f g:(num → A → real). " +
			"∀U V h k:(A → real).",
		Hypotheses: []string{
			"∀n:num. is_cond_exp(Ω, S, μ, G, f(n), g(n))",
			"real_measurable(Ω, S, U)",
			"real_measurable(Ω, G, V)",
			"real_integrable(Ω, S, μ, h)",
			"real_integrable(Ω, S, μ, k)",
			"measure_ae(Ω, S, μ, λx:A. real_converges_to(λn:num. f(n, x), U(x)))",
			"measure_ae(Ω, S, μ, λx:A. real_converges_to(λn:num. g(n, x), V(x)))",
			"∀n:num. measure_ae(Ω, S, μ, λx:A. |f(n, x)| ≤ h(x))",
			"∀n:num. measure_ae(Ω, S, μ, λx:A. |g(n, x)| ≤ k(x))",
		},
		Conclusion: "is_cond_exp(Ω, S, μ, G, U, V)",
		Abbrev: Abbrev{
			{Name: "event", Text: "λE:set(A). λq:(A → real). event_integral(Ω, S, μ, E, q)"},
			{Name: "eventSequence", Text: "λE:set(A). λq:(num → A → real). λn:num. «event»(E, q(n))"},
		},
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		G *Expr[Set[Set[A]]],
		f, g *Arrow2[Nat, A, Real],
		U, V, h, k *Arrow[A, Real],
		premises Fact,
	) {
		parts := a.Conjuncts(
			premises,
			"each input has the corresponding conditional expectation",
			"the input limit is ambient measurable",
			"the output limit is measurable for G",
			"the input bound is integrable",
			"the output bound is integrable",
			"the inputs converge almost everywhere",
			"the outputs converge almost everywhere",
			"the inputs are dominated almost everywhere",
			"the outputs are dominated almost everywhere")
		conditional, measurableU, measurableV := parts[0], parts[1], parts[2]
		integrableH, integrableK := parts[3], parts[4]
		convergesF, convergesG, dominatedF, dominatedG := parts[5], parts[6], parts[7], parts[8]
		setting := a.Have(
			"the first conditional expectation supplies the ambient setting",
			"measure_on(Ω, S, μ) ∧ sigma_algebra_on(Ω, G) ∧ G ⊆ S",
			By(
				conditional.At(a.TermAs[Nat]("0")),
				IsCondExpDef.At(Ω, S, μ, G,
					a.TermAs[Fun[A, Real]]("f(0)"), a.TermAs[Fun[A, Real]]("g(0)"))))
		measurable := a.Have(
			"each input and output is ambient measurable, being integrable",
			"∀n:num. real_measurable(Ω, S, f(n)) ∧ real_measurable(Ω, S, g(n))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				fn := b.TermAs[Fun[A, Real]]("f(n)")
				gn := b.TermAs[Fun[A, Real]]("g(n)")
				b.Show(
					"both are integrable in the defining relation",
					By(
						conditional.At(n),
						IsCondExpDef.At(Ω, S, μ, G, fn, gn),
						measure_integral.RealIntegrableDef.At(Ω, S, μ, fn),
						measure_integral.RealIntegrableDef.At(Ω, S, μ, gn)))
			}))
		ambientV := a.Have(
			"G-measurability of V implies ambient measurability",
			"real_measurable(Ω, S, V)",
			By(setting, measurableV, measurable_function.RealMeasurableSourceMono.At(Ω, G, S, V)))
		integrable := a.Have(
			"dominated convergence makes both limits integrable",
			"real_integrable(Ω, S, μ, U) ∧ real_integrable(Ω, S, μ, V)",
			By(
				measurable,
				dominatedF,
				dominatedG,
				setting,
				measurableU,
				ambientV,
				convergesF,
				convergesG,
				integrableH,
				integrableK,
				integral_convergence.DominatedConvergenceAE.At(Ω, S, μ, f, U, h),
				integral_convergence.DominatedConvergenceAE.At(Ω, S, μ, g, V, k)))
		events := a.Have(
			"the limits have the same integral over every conditioning event",
			"∀E:set(A). E ∈ G ⇒ «event»(E, U) = «event»(E, V)",
			Derive(func(b *Argument) {
				E := b.FixAs[Set[A]]("E")
				inG := b.Assume()
				matching := b.Have(
					"the two event-integral sequences coincide",
					"«eventSequence»(E, f) = «eventSequence»(E, g)",
					Derive(func(c *Argument) {
						c.Do(Funext())
						n := c.FixAs[Nat]("n")
						c.Show(
							"the conditional expectation at n gives this event identity",
							By(
								conditional.At(n),
								inG,
								IsCondExpDef.At(Ω, S, μ, G,
									c.TermAs[Fun[A, Real]]("f(n)"),
									c.TermAs[Fun[A, Real]]("g(n)"))))
					}))
				limits := b.Have(
					"dominated convergence identifies the limits of both event-integral sequences",
					"real_converges_to(«eventSequence»(E, f), «event»(E, U)) ∧ "+
						"real_converges_to(«eventSequence»(E, g), «event»(E, V))",
					BySets(
						measurable,
						dominatedF,
						dominatedG,
						inG,
						setting,
						measurableU,
						ambientV,
						convergesF,
						convergesG,
						integrableH,
						integrableK,
						event_integral.EventIntegralDominatedConvergence.At(Ω, S, μ, E, f, U, h),
						event_integral.EventIntegralDominatedConvergence.At(Ω, S, μ, E, g, V, k)))
				b.Show(
					"a common sequence has a unique limit",
					By(
						matching,
						limits,
						real_sequences.LimitUnique.At(
							b.TermAs[Fun[Nat, Real]]("«eventSequence»(E, f)"),
							b.TermAs[Real]("«event»(E, U)"),
							b.TermAs[Real]("«event»(E, V)"))))
			}))
		a.Show(
			"integrability, G-measurability and the event identities give the limiting relation",
			By(events, setting, integrable, measurableV, IsCondExpDef.At(Ω, S, μ, G, U, V)))
	}),
})}

// CondExpFiniteRangeFactor — multiplication by a signed finite-range G-measurable
// function preserves conditional expectation: restrict to its level events,
// scale each restriction, and add the finitely many contributions.
var CondExpFiniteRangeFactor = condExpFiniteRangeFactorThm{family.Add(registry.ProofEntry{
	Name: "CondExpFiniteRangeFactor",
	Key:  "prop_e25867ea17b2ae2b",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀X Y h:(A → real).",
		Hypotheses: []string{
			"is_cond_exp(Ω, S, μ, G, X, Y)",
			"real_measurable(Ω, G, h)",
			"finite(image(h, Ω))",
		},
		Conclusion: "is_cond_exp(Ω, S, μ, G, λx:A. h(x) * X(x), λx:A. h(x) * Y(x))",
		Abbrev: Abbrev{
			{Name: "cut", Text: "λD:set(A). λf:(A → real). λx:A. COND(x ∈ D, f(x), &0)"},
			{Name: "level", Text: "λΩ:set(A). λh:(A → real). λy:real. {x:A | x ∈ Ω ∧ h(x) = y}"},
			{Name: "piece", Text: "λh:(A → real). λf:(A → real). λy:real. λx:A. COND(h(x) = y, y * f(x), &0)"},
			{Name: "sumFunctions", Text: "λI:set(real). λF:(real → A → real). λx:A. Σ_{y∈I} F(y, x)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		congruentOnCarrier := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀G:set(set(A)). " +
				"∀X Y U V:(A → real).",
			Hypotheses: []string{"is_cond_exp(Ω, S, μ, G, X, Y)", "∀x:A. x ∈ Ω ⇒ X(x) = U(x) ∧ Y(x) = V(x)"},
			Conclusion: "is_cond_exp(Ω, S, μ, G, U, V)",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			G *Expr[Set[Set[A]]],
			X, Y, U, V *Arrow[A, Real],
			given Fact,
		) {
			relation := a.Unfolded(given, IsCondExpDef)
			measurable := a.Have(
				"the new output retains G-measurability",
				"real_measurable(Ω, G, V)",
				By(
					relation,
					measurable_function.RealMeasurableDef.At(Ω, G, Y),
					measurable_space.MeasurableCongruence.At(
						Ω, G, a.TermAs[Set[Real]]("𝕌"), a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"), Y, V),
					measurable_function.RealMeasurableDef.At(Ω, G, V)))
			events := a.Have(
				"the replacements preserve every conditioning-event integral",
				"∀E:set(A). E ∈ G ⇒ event_integral(Ω, S, μ, E, U) = event_integral(Ω, S, μ, E, V)",
				Derive(func(b *Argument) {
					E := b.FixAs[Set[A]]("E")
					inG := b.Assume()
					b.Show(
						"both event integrals equal those of the original pair",
						By(
							inG,
							relation,
							event_integral.EventIntegralEqOn.At(Ω, S, μ, E, X, U),
							event_integral.EventIntegralEqOn.At(Ω, S, μ, E, Y, V)))
				}))
			a.Show(
				"integrability, output measurability, and the event identities all transfer",
				By(
					events,
					relation,
					measurable,
					measure_integral.RealIntegrableEqOn.At(Ω, S, μ, X, U),
					measure_integral.RealIntegrableEqOn.At(Ω, S, μ, Y, V),
					IsCondExpDef.At(Ω, S, μ, G, U, V)))
		})
		restrictToEvent := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀G:set(set(A)). " +
				"∀X Y:(A → real). " +
				"∀D:set(A).",
			Hypotheses: []string{"is_cond_exp(Ω, S, μ, G, X, Y)", "D ∈ G"},
			Conclusion: "is_cond_exp(Ω, S, μ, G, «cut»(D, X), «cut»(D, Y))",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			G *Expr[Set[Set[A]]],
			X, Y *Arrow[A, Real],
			D *Expr[Set[A]],
			given Fact,
		) {
			relation := a.Unfolded(given, IsCondExpDef)
			measurable := a.Have(
				"restriction to D preserves G-measurability",
				"real_measurable(Ω, G, «cut»(D, Y))",
				By(relation, measurable_function.RealMeasurableOnEvent.At(Ω, G, D, Y)))
			events := a.Have(
				"the restricted pair agrees over each conditioning event",
				Statement{
					Binders:    "∀E:set(A).",
					Hypotheses: []string{"E ∈ G"},
					Conclusion: "event_integral(Ω, S, μ, E, «cut»(D, X)) = event_integral(Ω, S, μ, E, «cut»(D, Y))",
				},
				Derive(func(b *Argument) {
					E := b.FixAs[Set[A]]("E")
					inG := b.Assume()
					b.Show(
						"restriction reads the original identity on E intersect D",
						By(
							inG,
							relation,
							sigma_algebra.SigmaFiniteOperations.At(Ω, G),
							event_integral.EventIntegralRestrict.At(Ω, S, μ, E, D, X),
							event_integral.EventIntegralRestrict.At(Ω, S, μ, E, D, Y)))
				}))
			ambientParts := a.Conjuncts(
				a.Unfolded(relation, measure_space.MeasureOn),
				"the ambient sigma algebra",
				"the empty set has measure zero",
				"the measure is countably additive",
				"the conditioning sigma algebra",
				"conditioning events are ambient events",
				"the input is integrable",
				"the output is integrable",
				"the output is G-measurable",
				"the original event identities",
				"D is a conditioning event")
			ambientSigma, included, inG := ambientParts[0], ambientParts[4], ambientParts[9]
			a.Show(
				"both restrictions are integrable and satisfy the defining conditions",
				BySets(
					events,
					inG,
					ambientSigma,
					included,
					relation,
					measurable,
					event_integral.IntegrableOnEvent.At(Ω, S, μ, D, X),
					event_integral.IntegrableOnEvent.At(Ω, S, μ, D, Y),
					IsCondExpDef.At(
						Ω, S, μ, G, a.TermAs[Fun[A, Real]]("«cut»(D, X)"), a.TermAs[Fun[A, Real]]("«cut»(D, Y)"))))
		})
		finiteSums := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀G:set(set(A)). " +
				"∀F H:(real → A → real). " +
				"∀I:set(real).",
			Hypotheses: []string{"∀y:real. is_cond_exp(Ω, S, μ, G, F(y), H(y))", "finite(I)"},
			Conclusion: "is_cond_exp(Ω, S, μ, G, «sumFunctions»(I, F), «sumFunctions»(I, H))",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			G *Expr[Set[Set[A]]],
			F, H *Arrow2[Real, A, Real],
			I *Expr[Set[Real]],
			given Fact,
		) {
			a.Show(
				"finite-set induction adds one conditional-expectation pair at a time",
				ByInduction(finite_set.FiniteInductFresh, given,
					Case(
						"the empty sums are the zero linear combination",
						Simp(Fwd(real_sum.Clauses)),
						By(
							given,
							CondExpLinear.At(Ω, S, μ, G,
								a.TermAs[Fun[A, Real]]("F(&0)"), a.TermAs[Fun[A, Real]]("H(&0)"),
								a.TermAs[Fun[A, Real]]("F(&0)"), a.TermAs[Fun[A, Real]]("H(&0)"),
								a.TermAs[Real]("&0"), a.TermAs[Real]("&0")),
							real_ring.MulLeftZero,
							real_ring.AddRightId)),
					Case(
						"a fresh index contributes its pair to the existing sums",
						Derive(func(b *Argument) {
							b.FixAs[Real]("x")
							b.FixAs[Set[Real]]("s")
							step := b.Conjuncts(
								b.Assume(),
								"the sums over s satisfy the relation",
								"the index is fresh",
								"s is finite")
							sumF := b.TermAs[Fun[A, Real]]("«sumFunctions»(s, F)")
							sumH := b.TermAs[Fun[A, Real]]("«sumFunctions»(s, H)")
							addedF := b.TermAs[Fun[A, Real]]("λz:A. F(x, z) + «sumFunctions»(s, F, z)")
							addedH := b.TermAs[Fun[A, Real]]("λz:A. H(x, z) + «sumFunctions»(s, H, z)")
							added := b.Have(
								"linearity adds the new pair",
								"is_cond_exp(Ω, "+
									"    S, "+
									"    μ, "+
									"    G, "+
									"    λz:A. F(x, z) + «sumFunctions»(s, F, z), "+
									"    λz:A. H(x, z) + «sumFunctions»(s, H, z))",
								By(
									given,
									step[0],
									CondExpLinear.At(
										Ω,
										S,
										μ,
										G,
										b.TermAs[Fun[A, Real]]("F(x)"),
										b.TermAs[Fun[A, Real]]("H(x)"),
										sumF,
										sumH,
										b.TermAs[Real]("&1"),
										b.TermAs[Real]("&1")),
									real_ring.MulAC,
									real_ring.MulRightId))
							b.Show(
								"the insertion equations identify these functions with the larger sums",
								By(
									step[2],
									step[1],
									added,
									real_sum.Clauses,
									At(congruentOnCarrier, Ω, S, μ, G, addedF, addedH,
										b.TermAs[Fun[A, Real]]("«sumFunctions»(insert(x, s), F)"),
										b.TermAs[Fun[A, Real]]("«sumFunctions»(insert(x, s), H)"))))
						}))))
		})
		levelDecomposition := ctx.Lemma(Statement{
			Binders:    "∀Ω:set(A). ∀h f:(A → real). ∀x:A.",
			Hypotheses: []string{"x ∈ Ω"},
			Conclusion: "Σ_{y∈image(h, Ω)} «piece»(h, f, y, x) = h(x) * f(x)",
		}, func(a *Argument, Ω *Expr[Set[A]], h, f *Arrow[A, Real], x *Expr[A], inside Fact) {
			a.Show(
				"only the level containing x contributes",
				CalcEq(
					Leg(
						a.TermAs[Real]("Σ_{y∈image(h, Ω)} COND(y = h(x), h(x) * f(x), &0)"),
						"on the contributing level its value y equals h(x)",
						By(real_sum.Congruence.At(a.TermAs[Set[Real]]("image(h, Ω)"),
							a.TermAs[Fun[Real, Real]]("λy:real. «piece»(h, f, y, x)"),
							a.TermAs[Fun[Real, Real]]("λy:real. COND(y = h(x), h(x) * f(x), &0)")))),
					FinalLeg(
						"h(x) belongs to the image, so the delta sum is its contribution",
						BySets(
							inside,
							real_sum.Delta.At(a.TermAs[Real]("h(x) * f(x)"), a.TermAs[Set[Real]]("image(h, Ω)"), h.Apply(x))))))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			G *Expr[Set[Set[A]]],
			X, Y, h *Arrow[A, Real],
			given Fact,
		) {
			relation := a.Unfolded(given, IsCondExpDef)
			levels := a.Have(
				"every level of h inside Ω is a conditioning event",
				"∀y:real. «level»(Ω, h, y) ∈ G",
				Derive(func(b *Argument) {
					y := b.FixAs[Real]("y")
					intersection := b.Have(
						"a level is the intersection of its two closed rays",
						"«level»(Ω, h, y) = {x:A | x ∈ Ω ∧ h(x) ≤ y} ∩ {x:A | x ∈ Ω ∧ y ≤ h(x)}",
						BySets(real_construction.LessEqAntisym))
					b.Show(
						"the closed rays and their intersection are G-measurable",
						By(
							intersection,
							relation,
							measurable_function.RealMeasurableAtMost.At(Ω, G, h, y),
							measurable_function.RealMeasurableAtLeast.At(Ω, G, h, y),
							sigma_algebra.SigmaFiniteOperations.At(Ω, G)))
				}))
			pieces := a.Have(
				"each signed level contribution preserves conditional expectation",
				"∀y:real. is_cond_exp(Ω, S, μ, G, «piece»(h, X, y), «piece»(h, Y, y))",
				Derive(func(b *Argument) {
					y := b.FixAs[Real]("y")
					D := b.TermAs[Set[A]]("«level»(Ω, h, y)")
					cutX := b.TermAs[Fun[A, Real]]("«cut»(«level»(Ω, h, y), X)")
					cutY := b.TermAs[Fun[A, Real]]("«cut»(«level»(Ω, h, y), Y)")
					scaledX := b.TermAs[Fun[A, Real]]("λx:A. y * «cut»(«level»(Ω, h, y), X, x) + &0 * X(x)")
					scaledY := b.TermAs[Fun[A, Real]]("λx:A. y * «cut»(«level»(Ω, h, y), Y, x) + &0 * Y(x)")
					scaled := b.Have(
						"linearity scales the pair restricted to this level",
						"is_cond_exp(Ω, "+
							"    S, "+
							"    μ, "+
							"    G, "+
							"    λx:A. y * «cut»(«level»(Ω, h, y), X, x) + &0 * X(x), "+
							"    λx:A. y * «cut»(«level»(Ω, h, y), Y, x) + &0 * Y(x))",
						By(
							levels.At(y),
							given,
							At(restrictToEvent, Ω, S, μ, G, X, Y, D),
							CondExpLinear.At(Ω, S, μ, G, cutX, cutY, X, Y, y, b.TermAs[Real]("&0"))))
					b.Show(
						"on Ω these scaled restrictions are precisely the level contributions",
						BySets(
							scaled,
							At(congruentOnCarrier, Ω, S, μ, G, scaledX, scaledY,
								b.TermAs[Fun[A, Real]]("«piece»(h, X, y)"), b.TermAs[Fun[A, Real]]("«piece»(h, Y, y)")),
							real_ring.MulLeftZero,
							real_ring.MulRightZero,
							real_ring.AddRightId))
				}))
			inputPieces := a.TermAs[Fun2[Real, A, Real]]("«piece»(h, X)")
			outputPieces := a.TermAs[Fun2[Real, A, Real]]("«piece»(h, Y)")
			summed := a.Have(
				"add the finitely many level contributions",
				"is_cond_exp(Ω, "+
					"    S, "+
					"    μ, "+
					"    G, "+
					"    «sumFunctions»(image(h, Ω), «piece»(h, X)), "+
					"    «sumFunctions»(image(h, Ω), «piece»(h, Y)))",
				By(
					pieces,
					given,
					At(finiteSums, Ω, S, μ, G, inputPieces, outputPieces, a.TermAs[Set[Real]]("image(h, Ω)"))))
			a.Show(
				"the level decompositions equal h times X and h times Y on Ω",
				By(
					summed,
					At(levelDecomposition, Ω, h, X),
					At(levelDecomposition, Ω, h, Y),
					At(congruentOnCarrier, Ω, S, μ, G,
						a.TermAs[Fun[A, Real]]("«sumFunctions»(image(h, Ω), «piece»(h, X))"),
						a.TermAs[Fun[A, Real]]("«sumFunctions»(image(h, Ω), «piece»(h, Y))"),
						a.TermAs[Fun[A, Real]]("λx:A. h(x) * X(x)"), a.TermAs[Fun[A, Real]]("λx:A. h(x) * Y(x)"))))
		})
	}),
})}

// CondExpKnownFactor — an almost-everywhere bounded G-measurable factor passes
// through conditional expectation: approximate its nonnegative parts by simple
// functions, pass to dominated limits, and subtract.
var CondExpKnownFactor = condExpKnownFactorThm{family.Add(registry.ProofEntry{
	Name: "CondExpKnownFactor",
	Key:  "prop_badef76b22fe529f",
	Reading: "The bound is almost everywhere for the ambient " +
		"measure; no completeness or sign restriction on C is required.",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀X Y h:(A → real). " +
			"∀C:real.",
		Hypotheses: []string{
			"is_cond_exp(Ω, S, μ, G, X, Y)",
			"real_measurable(Ω, G, h)",
			"measure_ae(Ω, S, μ, λx:A. |h(x)| ≤ C)",
		},
		Conclusion: "is_cond_exp(Ω, S, μ, G, «product»(h, X), «product»(h, Y))",
		Abbrev: Abbrev{
			{Name: "product", Text: "λq:(A → real). λZ:(A → real). λx:A. q(x) * Z(x)"},
			{Name: "products", Text: "λr:(num → A → real). λZ:(A → real). λn:num. λx:A. r(n, x) * Z(x)"},
			{Name: "majorant", Text: "λZ:(A → real). λx:A. C * |Z(x)|"},
			{Name: "positive", Text: "λx:A. max(h(x), &0)"},
			{Name: "negative", Text: "λx:A. max(-h(x), &0)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		integrableMajorant := ctx.Lemma(measure_space.MeasureOn.Statement(Statement{
			Binders:    "∀X:(A → real). ∀C:real.",
			Hypotheses: []string{"real_integrable(Ω, S, μ, X)"},
			Conclusion: "real_integrable(Ω, S, μ, «majorant»(X))",
		}), func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			X *Arrow[A, Real],
			C *Expr[Real],
			premises Fact,
		) {
			absolute := a.Have(
				"absolute value preserves integrability",
				"real_integrable(Ω, S, μ, λx:A. |X(x)|)",
				By(premises, measure_space.MeasureOn.At(Ω, S, μ), measure_integral.IntegrableAbs.At(Ω, S, μ, X)))
			a.Show(
				"multiplication by C preserves integrability",
				By(premises, absolute, measure_integral.IntegrableScale))
		})
		approximate := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀G:set(set(A)). ∀h:(A → real).",
			Hypotheses: []string{
				"sigma_algebra_on(Ω, G)",
				"real_measurable(Ω, G, h)",
				"∀x:A. x ∈ Ω ⇒ &0 ≤ h(x)",
			},
			Conclusion: "∃s:(num → A → real). " +
				"    (∀n:num. measure_simple(Ω, G, s(n))) ∧ " +
				"    (∀n:num. ∀x:A. x ∈ Ω ⇒ &0 ≤ s(n, x) ∧ s(n, x) ≤ h(x)) ∧ " +
				"    (∀x:A. x ∈ Ω ⇒ (λn:num. s(n, x)) ⟶ h(x))",
		}, func(a *Argument, Ω *Expr[Set[A]], G *Expr[Set[Set[A]]], h *Arrow[A, Real], premises Fact) {
			s, simple := a.ObtainAs[Fun2[Nat, A, Real]](
				"choose increasing simple approximants to the embedded factor",
				"∃s:(num → A → real). "+
					"    (∀n:num. measure_simple(Ω, G, s(n))) ∧ "+
					"    (∀n:num. ∀x:A. x ∈ Ω ⇒ s(n, x) ≤ s(n + 1, x)) ∧ "+
					"    (∀n:num. ∀x:A. x ∈ Ω ⇒ extended_of_real(s(n, x)) ≤ extended_of_real(h(x))) ∧ "+
					"    (∀x:A. "+
					"        x ∈ Ω ⇒ "+
					"        extended_of_real(h(x)) = extended_sup(image(λn:num. extended_of_real(s(n, x)), 𝕌)))",
				By(
					premises,
					measurable_function.ExtendedMeasurableOfReal.At(Ω, G, h),
					measure_simple.SimpleApproximation.At(Ω, G,
						a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(h(x))"))))
			a.Take(s)
			a.Show(
				"the simple approximants are bounded and converge in the real numbers",
				SplitConjAll(
					Case(
						"each approximant is simple",
						By(simple)),
					Case(
						"the embedding reflects the pointwise upper bound",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							x := b.FixAs[A]("x")
							inside := b.Assume()
							b.Show(
								"simplicity gives nonnegativity and the embedding gives the upper bound",
								By(
									inside,
									premises,
									simple,
									measure_simple.NonnegSimpleDef.At(Ω, G, b.TermAs[Fun[A, Real]]("s(n)")),
									extended_nonneg_real.OfRealLe.At(b.TermAs[Real]("s(n, x)"), h.Apply(x))))
						})),
					Case(
						"the supremum identity gives pointwise real convergence",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							inside := b.Assume()
							nonnegative := b.Have(
								"the approximating sequence is nonnegative",
								"∀n:num. &0 ≤ s(n, x)",
								By(inside, simple, At(measure_simple.NonnegSimpleDef.Inst[A](), Ω, G)))
							b.Show(
								"a nonnegative increasing sequence converges to its embedded supremum",
								By(
									nonnegative,
									inside,
									premises,
									simple,
									extended_nonneg_real.SupSequenceOfReal.At(
										b.TermAs[Fun[Nat, Real]]("λn:num. s(n, x)"), h.Apply(x))))
						}))))
		})
		approximateProducts := ctx.Lemma(measure_space.MeasureOn.Statement(Statement{
			Binders: "∀s:(num → A → real). ∀h X:(A → real). ∀C:real.",
			Hypotheses: []string{
				"∀n:num. ∀x:A. x ∈ Ω ⇒ &0 ≤ s(n, x) ∧ s(n, x) ≤ h(x)",
				"∀x:A. x ∈ Ω ⇒ (λn:num. s(n, x)) ⟶ h(x)",
				"measure_ae(Ω, S, μ, λx:A. h(x) ≤ C)",
			},
			Conclusion: "measure_ae(Ω, S, μ, λx:A. (λn:num. «products»(s, X, n, x)) ⟶ «product»(h, X, x)) ∧ " +
				"(∀n:num. measure_ae(Ω, S, μ, λx:A. |«products»(s, X, n, x)| ≤ «majorant»(X, x)))",
		}), func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			s *Arrow2[Nat, A, Real],
			h, X *Arrow[A, Real],
			C *Expr[Real],
			premises Fact,
		) {
			a.Show(
				"the products converge almost everywhere under the same factor bound",
				SplitConj(
					Case(
						"multiplication preserves the pointwise limit",
						Derive(func(b *Argument) {
							pointwise := b.Have(
								"the products converge at every carrier point",
								"∀x:A. x ∈ Ω ⇒ (λn:num. «products»(s, X, n, x)) ⟶ «product»(h, X, x)",
								Derive(func(c *Argument) {
									x := c.FixAs[A]("x")
									inside := c.Assume()
									c.Show(
										"the second factor is a constant sequence",
										By(
											inside,
											premises,
											real_sequences.LimitConst.At(X.Apply(x)),
											real_sequences.LimitMul.At(c.TermAs[Fun[Nat, Real]]("λn:num. s(n, x)"),
												c.TermAs[Fun[Nat, Real]]("λn:num. X(x)"), h.Apply(x), X.Apply(x))))
								}))
							b.Show(
								"the pointwise product limit holds almost everywhere",
								By(pointwise, premises, measure_space.AEOfEverywhere))
						})),
					Case(
						"the factor bound dominates every product",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							pointwise := b.Have(
								"multiply the factor bound by the absolute value of X",
								"∀x:A. x ∈ Ω ∧ h(x) ≤ C ⇒ |«products»(s, X, n, x)| ≤ «majorant»(X, x)",
								Derive(func(c *Argument) {
									x := c.FixAs[A]("x")
									bound := c.Assume()
									c.Show(
										"the simple value is nonnegative and at most C",
										ByArith(
											bound,
											premises,
											real_sgn_abs.AbsMul.At(c.TermAs[Real]("s(n, x)"), X.Apply(x)),
											real_sgn_abs.AbsFixedIffNonneg.At(c.TermAs[Real]("s(n, x)")),
											real_sgn_abs.AbsNonneg.At(X.Apply(x))))
								}))
							b.Show(
								"the product inequality inherits the almost-everywhere factor bound",
								By(pointwise, premises, Where(measure_space.AEMono, "P", b.TermAs[Fun[A, Bool]]("λx:A. h(x) ≤ C"))))
						}))))
		})
		nonnegativeFactor := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀G:set(set(A)). " +
				"∀X Y h:(A → real). " +
				"∀C:real.",
			Hypotheses: []string{
				"is_cond_exp(Ω, S, μ, G, X, Y)", "real_measurable(Ω, G, h)",
				"∀x:A. x ∈ Ω ⇒ &0 ≤ h(x)", "measure_ae(Ω, S, μ, λx:A. h(x) ≤ C)",
			},
			Conclusion: "is_cond_exp(Ω, S, μ, G, «product»(h, X), «product»(h, Y))",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			G *Expr[Set[Set[A]]],
			X, Y, h *Arrow[A, Real],
			C *Expr[Real],
			premises Fact,
		) {
			parts := a.Conjuncts(
				premises,
				"the conditional expectation relation",
				"the factor is G-measurable",
				"the factor is nonnegative",
				"the factor is bounded almost everywhere")
			conditional, measurable, nonnegative, bounded := parts[0], parts[1], parts[2], parts[3]
			data := a.Unfolded(conditional, IsCondExpDef)
			s, approximation := a.ObtainAs[Fun2[Nat, A, Real]](
				"approximate the nonnegative factor by simple functions",
				"∃s:(num → A → real). "+
					"    (∀n:num. measure_simple(Ω, G, s(n))) ∧ "+
					"    (∀n:num. ∀x:A. x ∈ Ω ⇒ &0 ≤ s(n, x) ∧ s(n, x) ≤ h(x)) ∧ "+
					"    (∀x:A. x ∈ Ω ⇒ (λn:num. s(n, x)) ⟶ h(x))",
				By(nonnegative, data, measurable, approximate))
			conditionalProducts := a.Have(
				"finite-range factors pass through conditional expectation",
				"∀n:num. is_cond_exp(Ω, S, μ, G, «products»(s, X, n), «products»(s, Y, n))",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					b.Show(
						"a simple function is measurable and has finite range",
						By(
							approximation,
							conditional,
							measure_simple.NonnegSimpleDef.At(Ω, G, b.TermAs[Fun[A, Real]]("s(n)")),
							CondExpFiniteRangeFactor))
				}))
			ambientFactor := a.Have(
				"the factor is also ambient measurable",
				"real_measurable(Ω, S, h)",
				By(data, measurable, measurable_function.RealMeasurableSourceMono))
			measurableProducts := a.Have(
				"the limiting products have the required measurability",
				"real_measurable(Ω, S, «product»(h, X)) ∧ real_measurable(Ω, G, «product»(h, Y))",
				SplitConj(
					Case(
						"the input product is ambient measurable",
						By(
							data,
							ambientFactor,
							measure_space.MeasureOn.At(Ω, S, μ),
							measure_integral.RealIntegrableDef.At(Ω, S, μ, X),
							measurable_function.RealMeasurableMul.At(Ω, S, h, X))),
					Case(
						"the output product is G-measurable",
						By(data, measurable, measurable_function.RealMeasurableMul))))
			majorants := a.Have(
				"the two absolute-value majorants are integrable",
				"real_integrable(Ω, S, μ, «majorant»(X)) ∧ real_integrable(Ω, S, μ, «majorant»(Y))",
				By(data, At(integrableMajorant, Ω, S, μ, X, C), At(integrableMajorant, Ω, S, μ, Y, C)))
			limits := a.Have(
				"both product sequences converge almost everywhere and are dominated",
				"measure_ae(Ω, S, μ, λx:A. (λn:num. «products»(s, X, n, x)) ⟶ «product»(h, X, x)) ∧ "+
					"(∀n:num. measure_ae(Ω, S, μ, λx:A. |«products»(s, X, n, x)| ≤ «majorant»(X, x))) ∧ "+
					"measure_ae(Ω, S, μ, λx:A. (λn:num. «products»(s, Y, n, x)) ⟶ «product»(h, Y, x)) ∧ "+
					"(∀n:num. measure_ae(Ω, S, μ, λx:A. |«products»(s, Y, n, x)| ≤ «majorant»(Y, x)))",
				By(
					approximation,
					data,
					bounded,
					At(approximateProducts, Ω, S, μ, s, h, X, C),
					At(approximateProducts, Ω, S, μ, s, h, Y, C)))
			a.Show(
				"dominated limits preserve the conditional expectation relation",
				By(
					conditionalProducts,
					limits,
					measurableProducts,
					majorants,
					CondExpDominatedLimit.At(Ω, S, μ, G,
						a.TermAs[Fun2[Nat, A, Real]]("«products»(s, X)"),
						a.TermAs[Fun2[Nat, A, Real]]("«products»(s, Y)"),
						a.TermAs[Fun[A, Real]]("«product»(h, X)"),
						a.TermAs[Fun[A, Real]]("«product»(h, Y)"),
						a.TermAs[Fun[A, Real]]("«majorant»(X)"),
						a.TermAs[Fun[A, Real]]("«majorant»(Y)"))))
		})
		partsAlgebra := ctx.Lemma(
			"∀t:real. "+
				"    &0 ≤ max(t, &0) ∧ "+
				"    &0 ≤ max(-t, &0) ∧ "+
				"    max(t, &0) ≤ |t| ∧ "+
				"    max(-t, &0) ≤ |t| ∧ "+
				"    max(t, &0) - max(-t, &0) = t",
			func(a *Argument, t *Expr[Real]) {
				a.Show(
					"positive and negative parts are nonnegative, bounded by the modulus, and reconstruct t",
					ByArith(
						real_sup_inf.RealMaxDef.At(t, a.TermAs[Real]("&0")),
						real_sup_inf.RealMaxDef.At(a.TermAs[Real]("-t"), a.TermAs[Real]("&0")),
						real_sgn_abs.RealAbsDef.At(t)))
			})
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			G *Expr[Set[Set[A]]],
			X, Y, h *Arrow[A, Real],
			C *Expr[Real],
			premises Fact,
		) {
			measurableParts := a.Have(
				"the positive and negative parts are G-measurable",
				"real_measurable(Ω, G, «positive») ∧ real_measurable(Ω, G, «negative»)",
				By(
					premises,
					IsCondExpDef.At(Ω, S, μ, G, X, Y),
					measurable_function.RealMeasurableParts.At(Ω, G, h)))
			parts := a.Have(
				"the two nonnegative parts are bounded by the modulus and reconstruct the factor",
				"∀x:A. "+
					"    &0 ≤ «positive»(x) ∧ "+
					"    &0 ≤ «negative»(x) ∧ "+
					"    «positive»(x) ≤ |h(x)| ∧ "+
					"    «negative»(x) ≤ |h(x)| ∧ "+
					"    «positive»(x) - «negative»(x) = h(x)",
				By(partsAlgebra))
			pointwiseBound := a.Have(
				"a modulus bound bounds both parts",
				"∀x:A. x ∈ Ω ∧ |h(x)| ≤ C ⇒ «positive»(x) ≤ C ∧ «negative»(x) ≤ C",
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					bound := b.Assume()
					b.Show(
						"each part lies below the modulus",
						ByArith(parts, bound))
				}))
			boundedParts := a.Have(
				"both parts satisfy the almost-everywhere bound",
				"measure_ae(Ω, S, μ, λx:A. «positive»(x) ≤ C) ∧ measure_ae(Ω, S, μ, λx:A. «negative»(x) ≤ C)",
				By(
					pointwiseBound,
					premises,
					measure_space.AEMono.At(
						Ω,
						S,
						μ,
						a.TermAs[Fun[A, Bool]]("λx:A. |h(x)| ≤ C"),
						a.TermAs[Fun[A, Bool]]("λx:A. «positive»(x) ≤ C")),
					measure_space.AEMono.At(
						Ω,
						S,
						μ,
						a.TermAs[Fun[A, Bool]]("λx:A. |h(x)| ≤ C"),
						a.TermAs[Fun[A, Bool]]("λx:A. «negative»(x) ≤ C"))))
			conditionalParts := a.Have(
				"each nonnegative part passes through conditional expectation",
				"is_cond_exp(Ω, S, μ, G, «product»(«positive», X), «product»(«positive», Y)) ∧ "+
					"is_cond_exp(Ω, S, μ, G, «product»(«negative», X), «product»(«negative», Y))",
				By(
					parts,
					premises,
					measurableParts,
					boundedParts,
					At(nonnegativeFactor, Ω, S, μ, G, X, Y, a.TermAs[Fun[A, Real]]("«positive»"), C),
					At(nonnegativeFactor, Ω, S, μ, G, X, Y, a.TermAs[Fun[A, Real]]("«negative»"), C)))
			reconstruct := a.Have(
				"subtracting the part products recovers both original products",
				"(λx:A. &1 * «product»(«positive», X, x) + -&1 * «product»(«negative», X, x)) = "+
					"«product»(h, X) ∧ "+
					"(λx:A. &1 * «product»(«positive», Y, x) + -&1 * «product»(«negative», Y, x)) = «product»(h, Y)",
				SplitConj(
					Case(
						"the input products recombine",
						Derive(func(b *Argument) {
							b.Do(Funext())
							x := b.FixAs[A]("x")
							b.Show(
								"factor X and reconstruct h",
								CalcEq(
									Leg(
										b.TermAs[Real]("(«positive»(x) - «negative»(x)) * X(x)"),
										"distribute the input factor",
										ByArith()),
									FinalLeg(
										"the parts reconstruct h",
										By(parts.At(x)))))
						})),
					Case(
						"the output products recombine",
						Derive(func(b *Argument) {
							b.Do(Funext())
							x := b.FixAs[A]("x")
							b.Show(
								"factor Y and reconstruct h",
								CalcEq(
									Leg(
										b.TermAs[Real]("(«positive»(x) - «negative»(x)) * Y(x)"),
										"distribute the output factor",
										ByArith()),
									FinalLeg(
										"the parts reconstruct h",
										By(parts.At(x)))))
						}))))
			a.Show(
				"linearity recombines the two conditional expectation relations",
				By(
					reconstruct,
					conditionalParts,
					CondExpLinear.At(
						Ω,
						S,
						μ,
						G,
						a.TermAs[Fun[A, Real]]("«product»(«positive», X)"),
						a.TermAs[Fun[A, Real]]("«product»(«positive», Y)"),
						a.TermAs[Fun[A, Real]]("«product»(«negative», X)"),
						a.TermAs[Fun[A, Real]]("«product»(«negative», Y)"),
						a.TermAs[Real]("&1"),
						a.TermAs[Real]("-&1"))))
		})
	}),
})}
