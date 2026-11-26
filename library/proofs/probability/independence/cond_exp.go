// cond_exp.go — conditional expectations under independence.

package independence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/borel_function"
	"github.com/euc-ai/xugo/library/proofs/measure/conditional_expectation"
	"github.com/euc-ai/xugo/library/proofs/measure/event_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_simple"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// IndependentNonnegIntegral — an event independent of a σ-algebra comes out of
// the nonnegative integral of every function that σ-algebra measures: cut to
// the event, the function integrates to the event's probability times its
// integral. The simple functions rising to f are measurable for H, so each of
// their level sets is independent of E and E comes out of the simple integral
// of each cut; monotone convergence carries the identity to f.
var IndependentNonnegIntegral = independentNonnegIntegralThm{family.Add(registry.ProofEntry{
	Name: "IndependentNonnegIntegral",
	Key:  "prop_cf0dcf39d4428167",
	Reading: "f may take the value ∞ and its integral may be infinite: the product reads 0 " +
		"· ∞ as 0, and at μ(E) = 0 the cut, vanishing off a null set, integrates to 0 as well.",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G H:set(set(A)). " +
			"∀E:set(A). " +
			"∀f:(A → extended_nonneg_real).",
		Hypotheses: []string{
			"independent_sigma(Ω, S, μ, G, H)",
			"E ∈ G",
			"extended_measurable(Ω, H, f)",
		},
		Conclusion: "nonneg_integral(Ω, S, μ, λx:A. COND(x ∈ E, f(x), &0)) = " +
			"μ(E) * nonneg_integral(Ω, S, μ, f)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		G, H *Expr[Set[Set[A]]],
		E *Expr[Set[A]],
		f *Arrow[A, ExtendedNonnegReal],
		independent, event, measurable Fact,
	) {
		laws := a.Conjuncts(
			a.Unfolded(independent, IndependentSigmaDef),
			"μ is a probability on S",
			"G is a σ-algebra on Ω",
			"H is a σ-algebra on Ω",
			"G lies in S",
			"H lies in S",
			"an event of G and an event of H multiply")
		probability, sigmaH, gInS, hInS, factor := laws[0], laws[2], laws[3], laws[4], laws[5]
		measure := a.Have(
			"μ is a measure on S, and E is one of its events",
			"measure_on(Ω, S, μ) ∧ E ∈ S",
			By(
				probability,
				event,
				gInS,
				probability_space.ProbabilityOnDef.At(Ω, S, μ),
				set_basic.SubsetDef.At(G, S)))
		s, approximation := a.UnpackAs[Fun2[Nat, A, Real]](
			GroupPremises(sigmaH, measurable, measure_simple.SimpleApproximation.At(Ω, H, f)), "s")
		steps := a.Conjuncts(
			approximation,
			"each s(n) is simple for H",
			"the s(n) increase",
			"they lie below f",
			"f is their supremum")
		simpleH, increasing, supremum := steps[0], steps[1], steps[3]
		simpleS := a.Have(
			"each s(n) is simple for S as well, H lying in S",
			"∀n:num. measure_simple(Ω, S, s(n))",
			By(simpleH, hInS, measure_simple.NonnegSimpleDef, measurable_function.RealMeasurableSourceMono))
		cutIntegrals := a.Have(
			"cut to E, each s(n) stays simple, and its simple integral is μ(E) times that of s(n)",
			"∀n:num. "+
				"    measure_simple(Ω, S, λx:A. COND(x ∈ E, s(n, x), &0)) ∧ "+
				"    measure_simple_integral(Ω, μ, λx:A. COND(x ∈ E, s(n, x), &0)) = "+
				"    μ(E) * measure_simple_integral(Ω, μ, s(n))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				sn := b.TermAs[Fun[A, Real]]("s(n)")
				levels := b.Have(
					"E comes out of the measure of each level set of s(n), an event of H",
					"∀y:real. "+
						"    extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(n, x) = y} ∩ E) = "+
						"    μ(E) * (extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(n, x) = y}))",
					Derive(func(c *Argument) {
						y := c.FixAs[Real]("y")
						level := c.TermAs[Set[A]]("{x:A | x ∈ Ω ∧ s(n, x) = y}")
						split := c.Have(
							"independence splits the measure of the level set on E",
							"μ({x:A | x ∈ Ω ∧ s(n, x) = y} ∩ E) = μ(E) * μ({x:A | x ∈ Ω ∧ s(n, x) = y})",
							By(
								factor.At(E, level),
								event,
								sigmaH,
								simpleH.At(n),
								measure_simple.SimpleLevelSets.At(Ω, H, sn, y),
								set_algebra.InterComm.At(level, E)))
						value := c.TermAs[ExtendedNonnegReal]("extended_of_real(y)")
						c.Show(
							"the value regroups past μ(E)",
							By(
								split,
								extended_nonneg_real.MulAssoc.At(value, μ.Apply(E), μ.Apply(level)),
								extended_nonneg_real.MulAssoc.At(μ.Apply(E), value, μ.Apply(level)),
								extended_nonneg_real.MulComm.At(value, μ.Apply(E))))
					}))
				b.Show(
					"summed over the values of s(n), μ(E) comes out of the finite sum",
					By(
						measure,
						simpleS.At(n),
						levels,
						measure_simple.SimpleIntegralRestrict.At(Ω, S, μ, sn, E),
						measure_simple.NonnegSimpleDef.At(Ω, S, sn),
						extended_nonneg_real.SumScale.At(
							μ.Apply(E),
							b.TermAs[Fun[Real, ExtendedNonnegReal]](
								"λy:real. extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(n, x) = y})"),
							b.TermAs[Set[Real]]("image(s(n), Ω)")),
						measure_simple.SimpleIntegralDef.At(Ω, μ, sn)))
			}))
		cutIncreasing := a.Have(
			"the cuts of the s(n) to E still increase",
			"∀n:num. ∀x:A. x ∈ Ω ⇒ COND(x ∈ E, s(n, x), &0) ≤ COND(x ∈ E, s(n + 1, x), &0)",
			ByArith(increasing))
		cutSupremum := a.Have(
			"and they rise to f cut to E",
			Statement{
				Binders:    "∀x:A.",
				Hypotheses: []string{"x ∈ Ω"},
				Conclusion: "COND(x ∈ E, f(x), &0) = " +
					"extended_sup(image(λn:num. extended_of_real(COND(x ∈ E, s(n, x), &0)), 𝕌))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inside := b.Assume()
				b.Cases(b.TermAs[Bool]("x ∈ E"))
				b.When(
					"on E the cuts are the s(n), which rise to f",
					func(c *Argument, onE Fact) {
						c.Show(
							"f is their supremum at x",
							By(onE, inside, supremum.At(x)))
					})
				b.Otherwise(
					"off E every cut is 0, and so is their supremum",
					func(c *Argument, offE Fact) {
						zero := c.TermAs[ExtendedNonnegReal]("&0")
						bound := c.TermAs[ExtendedNonnegReal](
							"extended_sup(image(λn:num. extended_of_real(COND(x ∈ E, s(n, x), &0)), 𝕌))")
						c.Show(
							"a supremum of zeros lies between 0 and 0",
							By(
								offE,
								extended_nonneg_real.SupSequenceLeast.At(
									c.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. extended_of_real(COND(x ∈ E, s(n, x), &0))"),
									zero),
								extended_nonneg_real.ZeroLe.At(bound),
								extended_nonneg_real.LeRefl.At(zero),
								extended_nonneg_real.LeAntisym.At(bound, zero)))
					})
			}))
		a.Show(
			"monotone convergence on both sides, and μ(E) comes out of the supremum",
			By(
				supremum,
				cutSupremum,
				increasing,
				cutIncreasing,
				cutIntegrals,
				simpleS,
				measure,
				nonneg_integral.MonotoneConvergenceSimple.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun2[Nat, A, Real]]("λn:num. λx:A. COND(x ∈ E, s(n, x), &0)"),
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. COND(x ∈ E, f(x), &0)")),
				nonneg_integral.MonotoneConvergenceSimple.At(Ω, S, μ, s, f),
				extended_nonneg_real.SupSequenceScaleExtended.At(
					μ.Apply(E),
					a.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. measure_simple_integral(Ω, μ, s(n))"))))
	}),
})}

// IndependentEventIntegral — the integral of a real function over an event
// independent of the σ-algebra measuring it is the event's probability times
// the function's expectation. The positive and the negative part of X are
// extended_of_real(X(x)) and extended_of_real(−X(x)), extended_of_real taking
// a negative real to 0; E comes out of their nonnegative integrals
// (IndependentNonnegIntegral), and the finite value of a product is the
// product of the finite values.
var IndependentEventIntegral = independentEventIntegralThm{family.Add(registry.ProofEntry{
	Name: "IndependentEventIntegral",
	Key:  "prop_bcd4a19cf8d44bfb",
	Reading: "No integrability is asked of X: an infinite part reads as 0 " +
		"through extended_to_real on both sides, the probability of E being finite.",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G H:set(set(A)). " +
			"∀E:set(A). " +
			"∀X:(A → real).",
		Hypotheses: []string{
			"independent_sigma(Ω, S, μ, G, H)",
			"E ∈ G",
			"real_measurable(Ω, H, X)",
		},
		Conclusion: "event_integral(Ω, S, μ, E, X) = extended_to_real(μ(E)) * expectation(Ω, S, μ, X)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		G, H *Expr[Set[Set[A]]],
		E *Expr[Set[A]],
		X *Arrow[A, Real],
		independent, event, measurable Fact,
	) {
		negX := a.TermAs[Fun[A, Real]]("λx:A. -X(x)")
		positivePart := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(X(x))")
		negativePart := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-X(x))")
		parts := a.Have(
			"the positive and the negative part of X are measurable for H",
			"extended_measurable(Ω, H, λx:A. extended_of_real(X(x))) ∧ "+
				"extended_measurable(Ω, H, λx:A. extended_of_real(-X(x)))",
			By(
				measurable,
				independent,
				IndependentSigmaDef.At(Ω, S, μ, G, H),
				measurable_function.ExtendedMeasurableOfReal.At(Ω, H, X),
				measurable_function.RealMeasurableNeg.At(Ω, H, X),
				measurable_function.ExtendedMeasurableOfReal.At(Ω, H, negX)))
		factors := a.Have(
			"E comes out of the nonnegative integrals of both "+
				"parts, the parts of the cut being the cuts of the parts",
			"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(COND(x ∈ E, X(x), &0))) = "+
				"μ(E) * nonneg_integral(Ω, S, μ, λx:A. extended_of_real(X(x))) ∧ "+
				"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-COND(x ∈ E, X(x), &0))) = "+
				"μ(E) * nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-X(x)))",
			By(
				real_ring.NegZero,
				independent,
				event,
				parts,
				IndependentNonnegIntegral.At(Ω, S, μ, G, H, E, positivePart),
				IndependentNonnegIntegral.At(Ω, S, μ, G, H, E, negativePart)))
		positiveIntegral := a.TermAs[ExtendedNonnegReal](
			"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(X(x)))")
		negativeIntegral := a.TermAs[ExtendedNonnegReal](
			"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-X(x)))")
		difference := a.Have(
			"so the event integral is the difference of μ(E) times each part",
			"event_integral(Ω, S, μ, E, X) = "+
				"extended_to_real(μ(E)) * "+
				"extended_to_real(nonneg_integral(Ω, S, μ, λx:A. extended_of_real(X(x)))) - "+
				"extended_to_real(μ(E)) * "+
				"extended_to_real(nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-X(x))))",
			By(
				factors,
				event_integral.EventIntegralDef.At(Ω, S, μ, E, X),
				measure_integral.RealIntegralDef.At(Ω, S, μ, a.TermAs[Fun[A, Real]]("λx:A. COND(x ∈ E, X(x), &0)")),
				extended_nonneg_real.ToRealMul.At(μ.Apply(E), positiveIntegral),
				extended_nonneg_real.ToRealMul.At(μ.Apply(E), negativeIntegral)))
		probabilityE := a.TermAs[Real]("extended_to_real(μ(E))")
		a.Show(
			"which is μ(E) times the expectation, the difference of the parts",
			ByArith(
				difference,
				Scaled(probabilityE, measure_integral.RealIntegralDef.At(Ω, S, μ, X)),
				Scaled(probabilityE, probability_space.ExpectationDef.At(Ω, S, μ, X))))
	}),
})}

// IndependentCondExp — a random variable measurable for a σ-algebra
// independent of G has its expectation as conditional expectation given G.
// On each event of G the integral of X is the event's probability times E[X]
// (IndependentEventIntegral), which is the integral of the constant E[X] over
// the event; the constant is integrable on the probability space and
// measurable for G.
var IndependentCondExp = independentCondExpThm{family.Add(registry.ProofEntry{
	Name: "IndependentCondExp",
	Key:  "prop_f4976bd5b558aef7",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G H:set(set(A)). " +
			"∀X:(A → real).",
		Hypotheses: []string{
			"independent_sigma(Ω, S, μ, G, H)",
			"real_measurable(Ω, H, X)",
			"real_integrable(Ω, S, μ, X)",
		},
		Conclusion: "is_cond_exp(Ω, S, μ, G, X, λx:A. expectation(Ω, S, μ, X))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		G, H *Expr[Set[Set[A]]],
		X *Arrow[A, Real],
		independent, measurable, integrable Fact,
	) {
		laws := a.Conjuncts(
			a.Unfolded(independent, IndependentSigmaDef),
			"μ is a probability on S",
			"G is a σ-algebra on Ω",
			"H is a σ-algebra on Ω",
			"G lies in S",
			"H lies in S",
			"an event of G and an event of H multiply")
		probability, sigmaG, gInS := laws[0], laws[1], laws[3]
		heart := a.Have(
			"over each event of G, X integrates to the event's probability times E[X]",
			Statement{
				Binders:    "∀E:set(A).",
				Hypotheses: []string{"E ∈ G"},
				Conclusion: "event_integral(Ω, S, μ, E, X) = extended_to_real(μ(E)) * expectation(Ω, S, μ, X)",
			},
			By(independent, measurable, IndependentEventIntegral))
		mean := a.TermAs[Real]("expectation(Ω, S, μ, X)")
		constant := a.TermAs[Fun[A, Real]]("λx:A. expectation(Ω, S, μ, X)")
		averaged := a.Have(
			"which is the integral of the constant E[X] over the event",
			Statement{
				Binders:    "∀E:set(A).",
				Hypotheses: []string{"E ∈ G"},
				Conclusion: "event_integral(Ω, S, μ, E, X) = " +
					"event_integral(Ω, S, μ, E, λx:A. expectation(Ω, S, μ, X))",
			},
			Derive(func(b *Argument) {
				E := b.FixAs[Set[A]]("E")
				inG := b.Assume()
				b.Show(
					"a constant integrates over an event of S to its value times the event's mass",
					ByArith(
						heart.At(E),
						inG,
						gInS,
						probability,
						probability_space.ProbabilityOnDef.At(Ω, S, μ),
						set_basic.SubsetDef.At(G, S),
						event_integral.EventIntegralConst.At(Ω, S, μ, E, mean)))
			}))
		a.Show(
			"the constant is integrable and measurable for G, so it is a conditional expectation of X",
			By(
				averaged,
				sigmaG,
				gInS,
				probability,
				integrable,
				probability_space.ProbabilityOnDef.At(Ω, S, μ),
				probability_space.ExpectationConstant.At(Ω, S, μ, mean),
				measurable_function.RealMeasurableConst.At(Ω, G, mean),
				conditional_expectation.IsCondExpDef.At(Ω, S, μ, G, X, constant)))
	}),
})}

// IndependentFamilyCondExp — a Borel function of one variable of an
// independent family has its mean as conditional expectation given the
// variables of a block that leaves that variable out: the join over the
// block is independent of the join over {k}, and h(X(k)) is measurable for
// the join over {k}, X(k) being measurable for the σ-algebra it generates,
// which lies in that join.
var IndependentFamilyCondExp = independentFamilyCondExpThm{family.Add(registry.ProofEntry{
	Name: "IndependentFamilyCondExp",
	Key:  "prop_270b92f9c0e75699",
	Reading: "K need not be finite, and at K empty the join is the trivial σ-algebra {∅, Ω}. k ∉ K " +
		"is load-bearing, and so is h being Borel: for a non-Borel h, h ∘ X(k) need not be measurable " +
		"for the σ-algebra X(k) generates, its integrability making it measurable for S only.",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀J K:set(I). " +
			"∀X:(I → A → real). " +
			"∀k:I. " +
			"∀h:(real → real).",
		Hypotheses: []string{
			"independent_variable_family(Ω, S, μ, J, X)",
			"K ⊆ J",
			"k ∈ J",
			"k ∉ K",
			"real_measurable(𝕌, borel_sets(real_topology), h)",
			"real_integrable(Ω, S, μ, λx:A. h(X(k, x)))",
		},
		Conclusion: "is_cond_exp(Ω, " +
			"    S, " +
			"    μ, " +
			"    sigma_join(Ω, λj:I. pullback_sigma(Ω, X(j), borel_sets(real_topology)), K), " +
			"    λx:A. h(X(k, x)), " +
			"    λx:A. expectation(Ω, S, μ, λy:A. h(X(k, y))))",
		Abbrev: Abbrev{
			{Name: "pullbacks", Text: "λj:I. pullback_sigma(Ω, X(j), borel_sets(real_topology))"},
		},
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		J, K *Expr[Set[I]],
		X *Arrow2[I, A, Real],
		k *Expr[I],
		h *Arrow[Real, Real],
		independent, blockInJ, kInJ, kOutsideBlock, hBorel, integrable Fact,
	) {
		pullbacks := a.TermAs[Fun2[I, Set[A], Bool]]("«pullbacks»")
		block := a.TermAs[Set[Set[A]]]("sigma_join(Ω, «pullbacks», K)")
		single := a.TermAs[Set[Set[A]]]("sigma_join(Ω, «pullbacks», {k})")
		variable := a.TermAs[Fun[A, Real]]("X(k)")
		observed := a.TermAs[Fun[A, Real]]("λx:A. h(X(k, x))")
		own := a.TermAs[Set[Set[A]]]("«pullbacks»(k)")
		blocks := a.Have(
			"the variables' σ-algebras are independent, so are "+
				"their joins over the disjoint blocks K and {k} of J",
			"independent_sigma(Ω, S, μ, sigma_join(Ω, «pullbacks», K), sigma_join(Ω, «pullbacks», {k}))",
			BySets(
				independent,
				IndependentVariableFamilyDef.At(Ω, S, μ, J, X),
				blockInJ,
				kInJ,
				kOutsideBlock,
				IndependentFamilyGroups.At(Ω, S, μ, J, K, a.TermAs[Set[I]]("{k}"), pullbacks)))
		ownSigma := a.Have(
			"X(k) pulls back a σ-algebra on Ω, and is measurable for it",
			"sigma_algebra_on(Ω, «pullbacks»(k)) ∧ real_measurable(Ω, «pullbacks»(k), X(k))",
			By(borel_function.RealPullbackSigma.At(Ω, variable)))
		ownInSingle := a.Have(
			"that σ-algebra generates the join over {k}, so lies in it",
			"«pullbacks»(k) ⊆ sigma_join(Ω, «pullbacks», {k})",
			Simp(Fwd(sigma_algebra.SigmaJoinDef), Fwd(set_image.ImageClauses), Fwd(set_algebra.UnionsSing)),
			By(
				ownSigma,
				sigma_algebra.SigmaAlgebraOnDef.At(Ω, own),
				sigma_algebra.GeneratedSigmaAlgebra.At(Ω, own)))
		observedMeasurable := a.Have(
			"h is Borel, so h(X(k)) is measurable for the "+
				"σ-algebra X(k) generates, and so for the join over {k}",
			"real_measurable(Ω, sigma_join(Ω, «pullbacks», {k}), λx:A. h(X(k, x)))",
			By(
				ownSigma,
				ownInSingle,
				hBorel,
				borel_function.RealMeasurableCompose.At(Ω, own, variable, h),
				measurable_function.RealMeasurableSourceMono.At(Ω, own, single, observed)))
		a.Show(
			"so h(X(k)) is independent of the join over K, and its mean is its conditional expectation there",
			By(blocks, observedMeasurable, integrable, IndependentCondExp.At(Ω, S, μ, block, single, observed)))
	}),
})}
