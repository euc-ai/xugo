package nonneg_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_simple"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// NonnegIntegralAE — functions equal almost everywhere have the same
// integral. Take a measurable set N of measure zero holding every point of Ω
// where f and g differ. A simple function s below f on Ω, cut to 0 on N,
// stays simple and lies below g on Ω; it keeps its simple integral, since
// each level set of s loses only a part of N. So every simple integral below
// f is one below g, the integral of f is at most that of g, and the two
// functions trade places.
var NonnegIntegralAE = nonnegIntegralAEThm{family.Add(registry.ProofEntry{
	Name: "NonnegIntegralAE",
	Reading: "No measurability is read: a simple minorant set to zero " +
		"on a measurable null set stays simple with the same simple integral.",
	Key: "prop_83988b4e0a102562",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀f g:(A → extended_nonneg_real).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"measure_ae_eq(Ω, S, μ, f, g)",
		},
		Conclusion: "nonneg_integral(Ω, S, μ, f) = nonneg_integral(Ω, S, μ, g)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		below := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀f g:(A → extended_nonneg_real).",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"measure_ae_eq(Ω, S, μ, f, g)",
			},
			Conclusion: "nonneg_integral(Ω, S, μ, f) ≤ nonneg_integral(Ω, S, μ, g)",
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
			f, g *Arrow[A, ExtendedNonnegReal], measure, equal Fact) {
			laws := a.Conjuncts(
				a.Unfolded(measure, measure_space.MeasureOn),
				"the measurable sets form a sigma algebra",
				"the empty set has measure zero",
				"countable disjoint unions have the series of their measures")
			sigma := laws[0]
			closure := a.Unfolded(sigma, sigma_algebra.SigmaAlgebraOnDef)
			exceptional := a.Conjuncts(
				a.Unfolded(
					a.Unfolded(a.Unfolded(equal, measure_space.AEEqualDef), measure_space.AlmostEverywhereDef),
					measure_space.NullSetDef),
				"the points of Ω where f and g differ lie in Ω",
				"and in a measurable set of measure zero")
			_, null := a.UnpackAs[Set[A]](exceptional[1], "N")
			covering := a.Conjuncts(
				null,
				"N is measurable",
				"N has measure zero",
				"N holds every point of Ω where f and g differ")
			measurableN, zero := covering[0], covering[1]
			agree := a.Have(
				"f and g agree on Ω off N",
				"∀x:A. x ∈ Ω ∖ N ⇒ f(x) = g(x)",
				BySets(covering[2]))
			rest := a.Have(
				"what N leaves of Ω is measurable",
				"Ω ∖ N ∈ S",
				By(closure, measurableN, sigma, sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
			cut := a.Have(
				"a simple function below f on Ω, cut to 0 on N, is "+
					"simple, lies below g on Ω and keeps its simple integral",
				Statement{
					Binders: "∀s:(A → real).",
					Hypotheses: []string{
						"measure_simple(Ω, S, s)",
						"∀x:A. x ∈ Ω ⇒ extended_of_real(s(x)) ≤ f(x)",
					},
					Conclusion: "measure_simple(Ω, S, λx:A. COND(x ∈ Ω ∖ N, s(x), &0)) ∧ " +
						"(∀x:A. x ∈ Ω ⇒ extended_of_real(COND(x ∈ Ω ∖ N, s(x), &0)) ≤ g(x)) ∧ " +
						"measure_simple_integral(Ω, μ, λx:A. COND(x ∈ Ω ∖ N, s(x), &0)) = measure_simple_integral(Ω, μ, s)",
				},
				Derive(func(b *Argument) {
					s := b.FixAs[Fun[A, Real]]("s")
					given := b.Conjuncts(
						b.Assume(),
						"s is simple",
						"s lies below f on Ω")
					restricted := b.Conjuncts(
						GroupPremises(
							measure,
							given[0],
							rest,
							measure_simple.SimpleIntegralRestrict.At(Ω, S, μ, s, b.TermAs[Set[A]]("Ω ∖ N"))),
						"cut to Ω ∖ N, s stays simple",
						"its simple integral weighs each value of s by the part of its level set off N")
					levels := b.Have(
						"each level set of s loses only a part of N, of measure zero",
						"∀y:real. μ({x:A | x ∈ Ω ∧ s(x) = y} ∩ (Ω ∖ N)) = μ({x:A | x ∈ Ω ∧ s(x) = y})",
						Derive(func(c *Argument) {
							y := c.FixAs[Real]("y")
							level := c.TermAs[Set[A]]("{x:A | x ∈ Ω ∧ s(x) = y}")
							kept := c.TermAs[Set[A]]("{x:A | x ∈ Ω ∧ s(x) = y} ∩ (Ω ∖ N)")
							lost := c.TermAs[Set[A]]("{x:A | x ∈ Ω ∧ s(x) = y} ∖ ({x:A | x ∈ Ω ∧ s(x) = y} ∩ (Ω ∖ N))")
							measurable := c.Have(
								"the level set, its part off N and the rest are measurable",
								"{x:A | x ∈ Ω ∧ s(x) = y} ∈ S ∧ "+
									"{x:A | x ∈ Ω ∧ s(x) = y} ∩ (Ω ∖ N) ∈ S ∧ "+
									"{x:A | x ∈ Ω ∧ s(x) = y} ∖ ({x:A | x ∈ Ω ∧ s(x) = y} ∩ (Ω ∖ N)) ∈ S",
								By(
									sigma,
									given[0],
									rest,
									measure_simple.SimpleLevelSets.At(Ω, S, s, y),
									sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
							inside := c.Have(
								"the part off N lies in the level set, and the rest lies in N",
								"{x:A | x ∈ Ω ∧ s(x) = y} ∩ (Ω ∖ N) ⊆ {x:A | x ∈ Ω ∧ s(x) = y} ∧ "+
									"{x:A | x ∈ Ω ∧ s(x) = y} ∖ ({x:A | x ∈ Ω ∧ s(x) = y} ∩ (Ω ∖ N)) ⊆ N",
								BySets())
							vanishing := c.Have(
								"so the rest has measure zero",
								"μ({x:A | x ∈ Ω ∧ s(x) = y} ∖ ({x:A | x ∈ Ω ∧ s(x) = y} ∩ (Ω ∖ N))) = &0",
								By(
									measure,
									measurable,
									measurableN,
									inside,
									zero,
									measure_space.MeasureMono.At(Ω, S, μ, lost, b.TermAs[Set[A]]("N")),
									extended_nonneg_real.ZeroLe,
									extended_nonneg_real.LeAntisym))
							c.Show(
								"and the level set measures what its part off N does",
								By(
									measure,
									measurable,
									inside,
									vanishing,
									measure_space.MeasureAddDiff.At(Ω, S, μ, kept, level),
									extended_nonneg_real.AddZero))
						}))
					b.Show(
						"the cut function is simple, below g on Ω, with the same simple integral",
						SplitConjAll(
							Case(
								"it is simple",
								By(restricted[0])),
							Case(
								"off N it is s, below f, which is g there; on N it is 0",
								By(given[1], agree, extended_nonneg_real.ZeroLe)),
							Case(
								"its simple integral is that of s",
								Simp(Fwd(restricted[1]), Fwd(levels)),
								By(measure_simple.SimpleIntegralDef))))
				}))
			bounded := a.Have(
				"so the simple integral of a simple function below f on Ω is at most the integral of g",
				Statement{
					Binders: "∀s:(A → real).",
					Hypotheses: []string{
						"measure_simple(Ω, S, s)",
						"∀x:A. x ∈ Ω ⇒ extended_of_real(s(x)) ≤ f(x)",
					},
					Conclusion: "measure_simple_integral(Ω, μ, s) ≤ nonneg_integral(Ω, S, μ, g)",
				},
				Derive(func(b *Argument) {
					s := b.FixAs[Fun[A, Real]]("s")
					given := b.Assume()
					cutS := b.TermAs[Fun[A, Real]]("λx:A. COND(x ∈ Ω ∖ N, s(x), &0)")
					parts := b.Conjuncts(
						GroupPremises(given, cut.At(s)),
						"the cut function is simple",
						"it lies below g on Ω",
						"it keeps the simple integral of s")
					b.Show(
						"its integral is its simple integral, at most that of g",
						By(
							parts[0],
							parts[1],
							parts[2],
							measure,
							NonnegIntegralSimple.At(Ω, S, μ, cutS),
							NonnegIntegralMono.At(Ω, S, μ, b.TermAs[Fun[A, ExtendedNonnegReal]](
								"λx:A. extended_of_real(COND(x ∈ Ω ∖ N, s(x), &0))"), g)))
				}))
			a.Do(Unfold(NonnegIntegralDef))
			a.Show(
				"and so is the supremum of those simple integrals",
				By(bounded, extended_nonneg_real.SupLeast))
		})
		return ctx.Theorem(headline, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal], f, g *Arrow[A, ExtendedNonnegReal], measure, equal Fact) {
			swapped := a.Have(
				"g equals f almost everywhere too",
				"measure_ae_eq(Ω, S, μ, g, f)",
				By(equal, measure_space.AEEqualDef))
			a.Show(
				"each integral is at most the other",
				By(
					At(below, Ω, S, μ, f, g),
					At(below, Ω, S, μ, g, f),
					measure,
					equal,
					swapped,
					extended_nonneg_real.LeAntisym))
		})
	}),
})}

// Markov — t times the measure of the set where f is at least t is at most
// the integral of f. That set is measurable, f being measurable. The
// function equal to t on the set and 0 elsewhere is simple and lies below f
// on Ω, and its simple integral is t times the measure of the set.
var Markov = markovThm{family.Add(registry.ProofEntry{
	Name: "Markov",
	Reading: "Measurability of f is load-bearing: the level " +
		"set must lie in S because μ is unconstrained off S.",
	Key: "prop_87055cd4b352a86b",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀f:(A → extended_nonneg_real). " +
			"∀t:real.",
		Hypotheses: []string{"measure_on(Ω, S, μ)", "extended_measurable(Ω, S, f)", "&0 < t"},
		Conclusion: "extended_of_real(t) * μ({x:A | x ∈ Ω ∧ extended_of_real(t) ≤ f(x)}) ≤ " +
			"nonneg_integral(Ω, S, μ, f)",
		Abbrev: Abbrev{
			{Name: "level", Text: "{x:A | x ∈ Ω ∧ extended_of_real(t) ≤ f(x)}"},
			{Name: "indicator", Text: "λx:A. COND(x ∈ «level», t, &0)"},
		},
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
		f *Arrow[A, ExtendedNonnegReal], t *Expr[Real], measure, measurable, positive Fact) {
		laws := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")
		measurableLevel := a.Have(
			"the set where f is at least t is measurable",
			"«level» ∈ S",
			By(laws[0], measurable, measurable_function.ExtendedMeasurableAtLeast.At(Ω, S, f, t)))
		nonnegative := a.Have(
			"t is nonnegative",
			"&0 ≤ t",
			ByArith(positive))
		indicator := a.Conjuncts(
			GroupPremises(
				measure,
				measurableLevel,
				nonnegative,
				measure_simple.SimpleIntegralIndicator.At(Ω, S, μ, a.TermAs[Set[A]]("«level»"), t)),
			"t on the set and 0 elsewhere is simple",
			"its simple integral is t times the measure of the set")
		under := a.Have(
			"it lies below f on Ω",
			"∀x:A. x ∈ Ω ⇒ extended_of_real(«indicator»(x)) ≤ f(x)",
			By(extended_nonneg_real.ZeroLe))
		a.Show(
			"so t times the measure of the set, the integral of a "+
				"simple function below f, is at most the integral of f",
			By(
				indicator[0],
				indicator[1],
				under,
				measure,
				NonnegIntegralSimple.At(Ω, S, μ, a.TermAs[Fun[A, Real]]("«indicator»")),
				NonnegIntegralMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(«indicator»(x))"),
					f)))
	}),
})}

// IntegralZeroIffAE — a measurable function has integral 0 exactly when it
// is 0 almost everywhere. If the integral is 0: a value is nonzero exactly
// when it exceeds some 1/(n + 1), and the set where f does is measurable;
// 1/(n + 1) on it and 0 elsewhere is a simple function below f, so
// 1/(n + 1) times its measure is at most 0, and the set is null. The
// points where f is nonzero form the countable union of these null sets.
// Conversely f then equals 0 almost everywhere, and has the integral of 0.
var IntegralZeroIffAE = integralZeroIffAEThm{family.Add(registry.ProofEntry{
	Name: "IntegralZeroIffAE",
	Reading: "Measurability is read only by ⇒: a non-measurable " +
		"indicator of inner measure zero has lower integral zero.",
	Key: "prop_dbab5092fff9934c",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀f:(A → extended_nonneg_real).",
		Hypotheses: []string{"measure_on(Ω, S, μ)", "extended_measurable(Ω, S, f)"},
		Conclusion: "nonneg_integral(Ω, S, μ, f) = &0 ⇔ measure_ae(Ω, S, μ, λx:A. f(x) = &0)",
		Abbrev: Abbrev{
			{Name: "above", Text: "λn:num. {x:A | x ∈ Ω ∧ extended_of_real(real_inv(&n + &1)) < f(x)}"},
		},
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
		f *Arrow[A, ExtendedNonnegReal], measure, measurable Fact) {
		a.Iff()
		a.Forward(
			"an integral of 0 leaves no mass above any positive level",
			func(b *Argument, zero Fact) {
				laws := b.Conjuncts(
					b.Unfolded(measure, measure_space.MeasureOn),
					"the measurable sets form a sigma algebra",
					"the empty set has measure zero",
					"countable disjoint unions have the series of their measures")
				sigma := laws[0]
				rays := b.Have(
					"f pulls back every ray above a real level into S",
					"∀r:real. {x:A | x ∈ Ω ∧ extended_of_real(r) < f(x)} ∈ S",
					By(sigma, measurable, measurable_function.ExtendedMeasurableIffRay.At(Ω, S, f)))
				nonzero := b.Have(
					"a value is nonzero exactly when it exceeds some 1/(n + 1)",
					"∀y:extended_nonneg_real. y ≠ &0 ⇔ ∃n:num. extended_of_real(real_inv(&n + &1)) < y",
					Derive(func(c *Argument) {
						y := c.FixAs[ExtendedNonnegReal]("y")
						c.Iff()
						c.Forward(
							"a nonzero value exceeds some 1/(n + 1)",
							func(d *Argument, positive Fact) {
								below := d.SupposeNot()
								v, value := d.ObtainAs[Real](
									"y lies at or below 1, so it is not ∞: it is a real v ≥ 0",
									"∃v:real. &0 ≤ v ∧ y = extended_of_real(v)",
									By(
										below,
										extended_nonneg_real.ExtendedCases.At(y),
										extended_nonneg_real.OfRealNotInfinity,
										extended_nonneg_real.LtIffNotLe,
										extended_nonneg_real.LeInfinity,
										extended_nonneg_real.LeAntisym))
								vNonzero := d.Have(
									"v is not 0, as y is not",
									"v ≠ &0",
									By(Normalized, positive, value))
								vPositive := d.Have(
									"so v is positive",
									"&0 < v",
									ByArith(vNonzero, value))
								_, small := d.ObtainAs[Nat](
									"and v exceeds some 1/(n + 1)",
									"∃n:num. real_inv(&n + &1) < v",
									ByArith(vPositive, real_archimedean.ExistsReciprocalBelow.At(v)))
								d.Show(
									"so y exceeds its image after all",
									By(below, value, small, vPositive, extended_nonneg_real.OfRealLt))
							})
						c.Backward(
							"a value above some 1/(n + 1) is above 0",
							func(d *Argument, some Fact) {
								_, beyond := d.UnpackAs[Nat](some, "n")
								d.Show(
									"0 lies below every value",
									By(beyond, extended_nonneg_real.ZeroLe, extended_nonneg_real.LtIffNotLe))
							})
					}))
				nullLevels := b.Have(
					"each set where f exceeds 1/(n + 1) is null",
					"∀n:num. measure_null(Ω, S, μ, «above»(n))",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("n")
						level := c.TermAs[Real]("real_inv(&n + &1)")
						set := c.TermAs[Set[A]]("«above»(n)")
						measurableSet := c.Have(
							"it is measurable",
							"«above»(n) ∈ S",
							By(rays))
						positive := c.Have(
							"1/(n + 1) is positive",
							"&0 < real_inv(&n + &1) ∧ &0 ≤ real_inv(&n + &1)",
							ByArith(real_order_field.InvPos.At(c.TermAs[Real]("&n + &1"))))
						indicator := c.Conjuncts(
							GroupPremises(
								measure,
								measurableSet,
								positive,
								measure_simple.SimpleIntegralIndicator.At(Ω, S, μ, set, level)),
							"1/(n + 1) on the set and 0 elsewhere is simple",
							"its simple integral is 1/(n + 1) times the measure of the set")
						simple := c.TermAs[Fun[A, Real]]("λx:A. COND(x ∈ «above»(n), real_inv(&n + &1), &0)")
						under := c.Have(
							"it lies below f on Ω",
							"∀x:A. x ∈ Ω ⇒ extended_of_real(COND(x ∈ «above»(n), real_inv(&n + &1), &0)) ≤ f(x)",
							By(extended_nonneg_real.LtIffNotLe, extended_nonneg_real.LeTotal, extended_nonneg_real.ZeroLe))
						vanishing := c.Have(
							"so 1/(n + 1) times the measure of the set is at most the integral of f, which is 0",
							"extended_of_real(real_inv(&n + &1)) * μ(«above»(n)) = &0",
							By(
								indicator[0],
								indicator[1],
								under,
								measure,
								zero,
								NonnegIntegralSimple.At(Ω, S, μ, simple),
								NonnegIntegralMono.At(
									Ω,
									S,
									μ,
									c.TermAs[Fun[A, ExtendedNonnegReal]](
										"λx:A. extended_of_real(COND(x ∈ «above»(n), real_inv(&n + &1), &0))"),
									f),
								extended_nonneg_real.ZeroLe,
								extended_nonneg_real.LeAntisym))
						factor := c.Have(
							"the image of 1/(n + 1) lies above 0, so it is not 0",
							"extended_of_real(real_inv(&n + &1)) ≠ &0",
							By(
								positive,
								extended_nonneg_real.OfRealLt.At(c.TermAs[Real]("&0"), level),
								extended_nonneg_real.LtIffNotLe,
								extended_nonneg_real.LeRefl))
						massZero := c.Have(
							"so the measure is 0",
							"μ(«above»(n)) = &0",
							By(vanishing, factor, extended_nonneg_real.MulEqZero))
						inside := c.Have(
							"it lies in Ω",
							"«above»(n) ⊆ Ω",
							BySets())
						c.Show(
							"a measurable set of measure zero is null",
							By(inside, measurableSet, massZero, set_order.SubsetRefl, measure_space.NullSetDef))
					}))
				union := b.Have(
					"f is nonzero on Ω exactly on the union of those sets",
					"{x:A | x ∈ Ω ∧ ¬(f(x) = &0)} = ⋃image(«above», 𝕌)",
					BySets(nonzero))
				b.Show(
					"a countable union of null sets is null",
					Simp(Fwd(measure_space.AlmostEverywhereDef), Fwd(union)),
					By(
						measure,
						nullLevels,
						measure_space.NullCountableUnion.At(Ω, S, μ, b.TermAs[Fun[Nat, Set[A]]]("«above»"))))
			})
		a.Backward(
			"f equal to 0 almost everywhere has the integral of 0",
			func(b *Argument, ae Fact) {
				equal := b.Have(
					"f equals the zero function almost everywhere",
					"measure_ae_eq(Ω, S, μ, f, λx:A. &0)",
					By(ae, measure_space.AEEqualDef))
				b.Show(
					"so the two integrals agree, and that of 0 is 0",
					By(
						measure,
						equal,
						NonnegIntegralAE.At(Ω, S, μ, f, b.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. &0")),
						NonnegIntegralZero.At(Ω, S, μ)))
			})
	}),
})}

var FiniteIntegralAEFinite = finiteIntegralAEFiniteThm{family.Add(registry.ProofEntry{
	Name: "FiniteIntegralAEFinite",
	Reading: "Measurability is load-bearing: infinity on a set of inner " +
		"measure zero and positive outer measure has lower integral zero.",
	Key: "prop_79c7041fcdff3f2a",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀f:(A → extended_nonneg_real).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"extended_measurable(Ω, S, f)",
			"nonneg_integral(Ω, S, μ, f) ≠ extended_infinity",
		},
		Conclusion: "measure_ae(Ω, S, μ, λx:A. f(x) ≠ extended_infinity)",
		Abbrev: Abbrev{
			{Name: "infinite", Text: "{x:A | x ∈ Ω ∧ f(x) = extended_infinity}"},
			{Name: "indicator", Text: "λt:real. λx:A. COND(x ∈ «infinite», t, &0)"},
		},
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
		f *Arrow[A, ExtendedNonnegReal], measure, measurable, finite Fact) {
		laws := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")
		sigma := laws[0]
		inside := a.Have(
			"the set where f is ∞ lies in Ω",
			"«infinite» ⊆ Ω",
			BySets())
		measurableInfinite := a.Have(
			"the set where f is ∞ is measurable",
			"«infinite» ∈ S",
			By(sigma, measurable, measurable_function.ExtendedMeasurableInfinitySet.At(Ω, S, f)))
		scaled := a.Have(
			"for t > 0, t times its measure is at most the integral of f",
			"∀t:real. &0 < t ⇒ extended_of_real(t) * μ(«infinite») ≤ nonneg_integral(Ω, S, μ, f)",
			Derive(func(b *Argument) {
				t := b.FixAs[Real]("t")
				positive := b.Assume()
				nonnegative := b.Have(
					"t is nonnegative",
					"&0 ≤ t",
					ByArith(positive))
				indicator := b.Conjuncts(
					GroupPremises(
						measure,
						measurableInfinite,
						nonnegative,
						measure_simple.SimpleIntegralIndicator.At(Ω, S, μ, b.TermAs[Set[A]]("«infinite»"), t)),
					"t on the set and 0 elsewhere is simple",
					"its simple integral is t times the measure of the set")
				under := b.Have(
					"it lies below f on Ω, f being ∞ on the set",
					"∀x:A. x ∈ Ω ⇒ extended_of_real(«indicator»(t, x)) ≤ f(x)",
					By(extended_nonneg_real.LeInfinity, extended_nonneg_real.ZeroLe))
				b.Show(
					"so its integral, t times the measure of the set, is at most that of f",
					By(
						indicator[0],
						indicator[1],
						under,
						measure,
						NonnegIntegralSimple.At(Ω, S, μ, b.TermAs[Fun[A, Real]]("«indicator»(t)")),
						NonnegIntegralMono.At(
							Ω,
							S,
							μ,
							b.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(«indicator»(t, x))"),
							f)))
			}))
		_, integral := a.ObtainAs[Real](
			"the integral of f is a real w ≥ 0",
			"∃w:real. &0 ≤ w ∧ nonneg_integral(Ω, S, μ, f) = extended_of_real(w)",
			By(
				finite,
				extended_nonneg_real.ExtendedCases.At(a.TermAs[ExtendedNonnegReal]("nonneg_integral(Ω, S, μ, f)"))))
		finiteMass := a.Have(
			"at t = 1 the measure of the set is at most w, so it is not ∞",
			"μ(«infinite») ≠ extended_infinity",
			By(
				a.Have(
					"1 is positive",
					"&0 < &1",
					ByArith()),
				scaled.At(a.TermAs[Real]("&1")),
				integral,
				extended_nonneg_real.MulOne,
				extended_nonneg_real.MulComm,
				extended_nonneg_real.LeInfinity,
				extended_nonneg_real.LeAntisym,
				extended_nonneg_real.OfRealNotInfinity))
		_, mass := a.ObtainAs[Real](
			"it is a real v ≥ 0",
			"∃v:real. &0 ≤ v ∧ μ(«infinite») = extended_of_real(v)",
			By(
				finiteMass,
				extended_nonneg_real.ExtendedCases.At(a.TermAs[ExtendedNonnegReal]("μ(«infinite»)"))))
		vanishing := a.Have(
			"and v is 0: a positive v would make (w + 1)/v times it, w + 1, at most w",
			"μ(«infinite») = &0",
			Derive(func(b *Argument) {
				nonzero := b.SupposeNot()
				vNonzero := b.Have(
					"v is not 0",
					"v ≠ &0",
					By(nonzero, mass))
				ratio := b.Have(
					"so (w + 1)/v is positive, and times v it is w + 1",
					"&0 < (w + &1) / v ∧ &0 ≤ (w + &1) / v ∧ (w + &1) / v * v = w + &1",
					ByArith(vNonzero, mass, integral))
				product := b.Have(
					"so (w + 1)/v times the measure of the set is w + 1",
					"extended_of_real((w + &1) / v) * μ(«infinite») = extended_of_real(w + &1)",
					By(ratio, mass, extended_nonneg_real.OfRealMul))
				bound := b.Have(
					"which is at most w",
					"w + &1 ≤ w",
					By(
						scaled.At(b.TermAs[Real]("(w + &1) / v")),
						ratio,
						product,
						integral,
						extended_nonneg_real.OfRealLe))
				b.Show(
					"impossible",
					ByArith(bound))
			}))
		exceptional := a.Have(
			"the points of Ω where f is not finite are those where it is ∞",
			"{x:A | x ∈ Ω ∧ ¬(f(x) ≠ extended_infinity)} = «infinite»",
			BySets())
		a.Show(
			"so they form a measurable set of measure zero",
			Simp(Fwd(measure_space.AlmostEverywhereDef), Fwd(exceptional)),
			By(inside, measurableInfinite, vanishing, set_order.SubsetRefl, measure_space.NullSetDef))
	}),
})}

// SubSigmaIntegral — on a sub-sigma-algebra G of S the integral of a
// G-measurable function is the same. A G-simple function is S-simple with
// the same simple integral, which gives ≤. For ≥, take an S-simple s below
// f on Ω and V its values together with 0. At each point t(x), the largest
// member of V that f(x) reaches, lies between s(x) and f(x); t takes its
// values in V, and t exceeds a level c exactly where f reaches the least
// member of V above c, a set of G, since every superlevel set of f is. So t
// is G-simple, and the simple integral of s is at most that of t.
var SubSigmaIntegral = subSigmaIntegralThm{family.Add(registry.ProofEntry{
	Name: "SubSigmaIntegral",
	Reading: "G-measurability of f is load-bearing: with G = {∅, Ω} and f " +
		"the indicator of an S-set of positive measure, the G-integral is zero.",
	Key: "prop_70d05c729629d031",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀f:(A → extended_nonneg_real).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"sigma_algebra_on(Ω, G)",
			"G ⊆ S",
			"extended_measurable(Ω, G, f)",
		},
		Conclusion: "nonneg_integral(Ω, G, μ, f) = nonneg_integral(Ω, S, μ, f)",
		Abbrev: Abbrev{
			{Name: "minorants", Text: "λT:set(set(A)). " +
				"    {r:extended_nonneg_real | " +
				"        ∃s:(A → real). " +
				"            measure_simple(Ω, T, s) ∧ " +
				"            (∀x:A. x ∈ Ω ⇒ extended_of_real(s(x)) ≤ f(x)) ∧ " +
				"            r = measure_simple_integral(Ω, μ, s)}"},
		},
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
		G *Expr[Set[Set[A]]], f *Arrow[A, ExtendedNonnegReal], measure, sigmaG, sub, measurable Fact) {
		laws := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")
		sigmaS := laws[0]
		subMeasure := a.Have(
			"μ is a measure on G",
			"measure_on(Ω, G, μ)",
			By(measure, sigmaG, sub, measure_space.SubSigmaMeasure.At(Ω, S, μ, G)))
		simpleS := a.Have(
			"a G-simple function is S-simple",
			"∀s:(A → real). measure_simple(Ω, G, s) ⇒ measure_simple(Ω, S, s)",
			Derive(func(b *Argument) {
				s := b.FixAs[Fun[A, Real]]("s")
				parts := b.Conjuncts(
					b.Unfolded(b.Assume(), measure_simple.NonnegSimpleDef),
					"s is G-measurable",
					"s takes finitely many values on Ω",
					"s is nonnegative on Ω")
				measurableS := b.Have(
					"its rays lie in G, so in S",
					"real_measurable(Ω, S, s)",
					By(
						sigmaG,
						parts[0],
						measurable_function.RealMeasurableIffRay.At(Ω, G, s),
						sigmaS,
						sub,
						set_basic.SubsetDef,
						measurable_function.RealMeasurableIffRay.At(Ω, S, s)))
				b.Show(
					"and it keeps its values",
					By(measurableS, parts[1], parts[2], measure_simple.NonnegSimpleDef))
			}))
		dominated := a.Have(
			"the simple integral of an S-simple function below f on Ω is at most the G-integral of f",
			Statement{
				Binders: "∀s:(A → real).",
				Hypotheses: []string{
					"measure_simple(Ω, S, s)",
					"∀x:A. x ∈ Ω ⇒ extended_of_real(s(x)) ≤ f(x)",
				},
				Conclusion: "measure_simple_integral(Ω, μ, s) ≤ nonneg_integral(Ω, G, μ, f)",
			},
			Derive(func(b *Argument) {
				s := b.FixAs[Fun[A, Real]]("s")
				given := b.Conjuncts(
					b.Assume(),
					"s is S-simple",
					"s lies below f on Ω")
				parts := b.Conjuncts(
					b.Unfolded(given[0], measure_simple.NonnegSimpleDef),
					"s is S-measurable",
					"s takes finitely many values on Ω",
					"s is nonnegative on Ω")
				_, vDef := b.LetAs[Set[Real]]("V", "insert(&0, image(s, Ω))")
				values := b.Have(
					"V is finite and holds 0 and the values of s on Ω, all of them nonnegative",
					"finite(V) ∧ &0 ∈ V ∧ (∀x:A. x ∈ Ω ⇒ s(x) ∈ V) ∧ (∀y:real. y ∈ V ⇒ &0 ≤ y)",
					By(
						vDef,
						parts[1],
						parts[2],
						finite_set.FiniteInsert,
						set_basic.InInsert,
						set_basic.InImage,
						real_order_ring.LessEqRefl))
				t, tDef := b.LetAs[Fun[A, Real]]("t", "λx:A. sup({y:real | y ∈ V ∧ extended_of_real(y) ≤ f(x)})")
				reached := b.Have(
					"at each point of Ω, t is the largest member of V that f reaches",
					Statement{
						Binders:    "∀x:A.",
						Hypotheses: []string{"x ∈ Ω"},
						Conclusion: "t(x) ∈ V ∧ " +
							"extended_of_real(t(x)) ≤ f(x) ∧ " +
							"(∀y:real. y ∈ V ∧ extended_of_real(y) ≤ f(x) ⇒ y ≤ t(x))",
					},
					Derive(func(c *Argument) {
						c.FixAs[A]("x")
						c.Assume()
						reachable := c.TermAs[Set[Real]]("{y:real | y ∈ V ∧ extended_of_real(y) ≤ f(x)}")
						inside := c.Have(
							"the members of V that f(x) reaches lie in V",
							"{y:real | y ∈ V ∧ extended_of_real(y) ≤ f(x)} ⊆ V",
							BySets())
						finiteReach := c.Have(
							"so they form a finite set",
							"finite({y:real | y ∈ V ∧ extended_of_real(y) ≤ f(x)})",
							By(inside, values, finite_set.FiniteSubset))
						nonempty := c.Have(
							"which holds 0, as f(x) reaches 0",
							"{y:real | y ∈ V ∧ extended_of_real(y) ≤ f(x)} ≠ ∅",
							BySets(values, extended_nonneg_real.ZeroLe))
						c.Show(
							"the supremum of a finite nonempty set is its largest member",
							Simp(Fwd(tDef)),
							By(finiteReach, nonempty, real_sup_inf.SupFiniteAttained.At(reachable)))
					}))
				lowerS := b.Have(
					"s lies below t on Ω",
					"∀x:A. x ∈ Ω ⇒ s(x) ≤ t(x)",
					By(values, given[1], reached))
				rayT := b.Have(
					"t exceeds each level c on a set of G",
					"∀c:real. {x:A | x ∈ Ω ∧ c < t(x)} ∈ G",
					Derive(func(c *Argument) {
						c.FixAs[Real]("c")
						aboveC := c.TermAs[Set[Real]]("{y:real | y ∈ V ∧ c < y}")
						c.Cases(c.Term("{y:real | y ∈ V ∧ c < y} = ∅"))
						c.When(
							"no member of V lies above c, and t takes its values in V",
							func(d *Argument, none Fact) {
								empty := d.Have(
									"so t exceeds c nowhere on Ω",
									"{x:A | x ∈ Ω ∧ c < t(x)} = ∅",
									BySets(none, reached))
								d.Show(
									"and the empty set lies in G",
									By(empty, sigmaG, sigma_algebra.SigmaFiniteOperations.At(Ω, G)))
							})
						c.Otherwise(
							"t exceeds c exactly where f reaches the least member of V above c",
							func(d *Argument, some Fact) {
								within := d.Have(
									"the members of V above c lie in V",
									"{y:real | y ∈ V ∧ c < y} ⊆ V",
									BySets())
								finiteAbove := d.Have(
									"so they form a finite set",
									"finite({y:real | y ∈ V ∧ c < y})",
									By(values, within, finite_set.FiniteSubset))
								least := d.Have(
									"which has a least member",
									"inf({y:real | y ∈ V ∧ c < y}) ∈ {y:real | y ∈ V ∧ c < y} ∧ "+
										"(∀y:real. y ∈ {y:real | y ∈ V ∧ c < y} ⇒ inf({y:real | y ∈ V ∧ c < y}) ≤ y)",
									By(some, finiteAbove, real_sup_inf.InfFiniteAttained.At(aboveC)))
								m, lowest := d.ObtainAs[Real](
									"so there is a member m of V above c, below every member of V above c",
									"∃m:real. m ∈ V ∧ c < m ∧ (∀y:real. y ∈ V ∧ c < y ⇒ m ≤ y)",
									By(least))
								pointwise := d.Have(
									"at a point of Ω, t exceeds c exactly when f reaches m",
									"∀x:A. x ∈ Ω ⇒ (c < t(x) ⇔ extended_of_real(m) ≤ f(x))",
									Derive(func(e *Argument) {
										x := e.FixAs[A]("x")
										point := e.Conjuncts(
											GroupPremises(e.Assume(), reached.At(x)),
											"t(x) is in V",
											"f(x) reaches t(x)",
											"t(x) is the largest member of V that f(x) reaches")
										e.Iff()
										e.Forward(
											"t(x) is a member of V above c, so at least m, and f(x) reaches m",
											func(g *Argument, above Fact) {
												g.Show(
													"the image of m lies below that of t(x)",
													By(
														above,
														point[0],
														point[1],
														lowest,
														values,
														extended_nonneg_real.OfRealLe,
														extended_nonneg_real.LeTrans))
											})
										e.Backward(
											"f(x) reaches m, a member of V above c, so t(x) is at least m",
											func(g *Argument, reaches Fact) {
												g.Show(
													"and t(x) lies above c",
													By(reaches, lowest, point[2], real_order_ring.LessThanLessEqTrans))
											})
									}))
								same := d.Have(
									"so t exceeds c exactly where f reaches m",
									"{x:A | x ∈ Ω ∧ c < t(x)} = {x:A | x ∈ Ω ∧ extended_of_real(m) ≤ f(x)}",
									BySets(pointwise))
								d.Show(
									"a superlevel set of f, measurable for G",
									By(same, sigmaG, measurable, measurable_function.ExtendedMeasurableAtLeast.At(Ω, G, f, m)))
							})
					}))
				finiteValues := b.Have(
					"the values of t on Ω lie in the finite set V",
					"finite(image(t, Ω))",
					By(
						values,
						b.Have(
							"they lie in V",
							"image(t, Ω) ⊆ V",
							BySets(reached)),
						finite_set.FiniteSubset))
				simpleT := b.Have(
					"so t is G-simple: G-measurable, with finitely many values, all nonnegative",
					"measure_simple(Ω, G, t)",
					By(
						sigmaG,
						rayT,
						measurable_function.RealMeasurableIffRay.At(Ω, G, t),
						finiteValues,
						values,
						reached,
						measure_simple.NonnegSimpleDef))
				b.Show(
					"the simple integral of s is at most that of t, its integral on G, at most that of f",
					By(
						measure,
						given[0],
						simpleT,
						simpleS.At(t),
						lowerS,
						measure_simple.SimpleIntegralMono.At(Ω, S, μ, s, t),
						subMeasure,
						NonnegIntegralSimple.At(Ω, G, μ, t),
						reached,
						NonnegIntegralMono.At(
							Ω,
							G,
							μ,
							b.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(t(x))"),
							f),
						extended_nonneg_real.LeTrans))
			}))
		lower := a.Have(
			"the G-integral is at most the S-integral, every G-simple minorant being an S-simple one",
			"nonneg_integral(Ω, G, μ, f) ≤ nonneg_integral(Ω, S, μ, f)",
			Derive(func(b *Argument) {
				b.Do(Unfold(NonnegIntegralDef))
				fewer := b.Have(
					"the simple integrals below f for G are among those for S",
					"«minorants»(G) ⊆ «minorants»(S)",
					BySets(simpleS))
				b.Show(
					"so the supremum for G is at most that for S",
					By(fewer, extended_nonneg_real.SupMono))
			}))
		upper := a.Have(
			"the S-integral is at most the G-integral",
			"nonneg_integral(Ω, S, μ, f) ≤ nonneg_integral(Ω, G, μ, f)",
			Derive(func(b *Argument) {
				b.Do(Unfold(NonnegIntegralDef))
				b.Show(
					"every simple integral below f for S is at most the G-integral",
					By(dominated, extended_nonneg_real.SupLeast))
			}))
		a.Show(
			"the two integrals bound each other",
			By(lower, upper, extended_nonneg_real.LeAntisym))
	}),
})}

// Chebyshev — t² times the measure of the set where |f| is at least t is at
// most the integral of f². That set is measurable, |f| being measurable. The
// function equal to t² on it and 0 elsewhere is simple and lies below f² on
// Ω, since t ≤ |f(x)| gives t² ≤ f(x)²; its simple integral is t² times the
// measure of the set.
var Chebyshev = chebyshevThm{family.Add(registry.ProofEntry{
	Name: "Chebyshev",
	Reading: "The positivity of t is load-bearing: for t " +
		"< 0 the level set is all of Ω while t·t is positive.",
	Key: "prop_aa0dc61fcddc8302",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀f:(A → real). " +
			"∀t:real.",
		Hypotheses: []string{"measure_on(Ω, S, μ)", "real_measurable(Ω, S, f)", "&0 < t"},
		Conclusion: "extended_of_real(t * t) * μ({x:A | x ∈ Ω ∧ t ≤ |f(x)|}) ≤ " +
			"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(f(x) * f(x)))",
		Abbrev: Abbrev{
			{Name: "level", Text: "{x:A | x ∈ Ω ∧ t ≤ |f(x)|}"},
			{Name: "indicator", Text: "λx:A. COND(x ∈ «level», t * t, &0)"},
		},
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
		f *Arrow[A, Real], t *Expr[Real], measure, measurable, positive Fact) {
		laws := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")
		sigma := laws[0]
		measurableLevel := a.Have(
			"where |f| is at least t is a measurable set, |f| being measurable",
			"«level» ∈ S",
			By(
				sigma,
				measurable,
				measurable_function.RealMeasurableAbs.At(Ω, S, f),
				measurable_function.RealMeasurableAtLeast.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. |f(x)|"), t)))
		square := a.Have(
			"t² is nonnegative",
			"&0 ≤ t * t",
			ByArith(positive))
		indicator := a.Conjuncts(
			GroupPremises(
				measure,
				measurableLevel,
				square,
				measure_simple.SimpleIntegralIndicator.At(
					Ω, S, μ, a.TermAs[Set[A]]("«level»"), a.TermAs[Real]("t * t"))),
			"t² on the set and 0 elsewhere is simple",
			"its simple integral is t² times the measure of the set")
		squares := a.Have(
			"where t ≤ |f(x)|, t² is at most f(x)², which is nonnegative",
			"∀x:A. t ≤ |f(x)| ⇒ t * t ≤ f(x) * f(x) ∧ &0 ≤ f(x) * f(x)",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				bound := b.Assume()
				b.Show(
					"squaring keeps the order of nonnegative numbers",
					ByArith(positive, bound))
			}))
		under := a.Have(
			"so the function lies below f² on Ω",
			"∀x:A. x ∈ Ω ⇒ extended_of_real(«indicator»(x)) ≤ extended_of_real(f(x) * f(x))",
			By(squares, extended_nonneg_real.OfRealLe, extended_nonneg_real.ZeroLe))
		a.Show(
			"and t² times the measure of the set, its integral, is at most the integral of f²",
			By(
				indicator[0],
				indicator[1],
				under,
				measure,
				NonnegIntegralSimple.At(Ω, S, μ, a.TermAs[Fun[A, Real]]("«indicator»")),
				NonnegIntegralMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(«indicator»(x))"),
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(f(x) * f(x))"))))
	}),
})}
