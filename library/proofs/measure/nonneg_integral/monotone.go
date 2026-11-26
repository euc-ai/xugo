// monotone.go — the monotone convergence theorem on a measure space: for a
// rising sequence of measurable [0, ∞]-valued functions, the integral of
// their pointwise supremum is the supremum of their integrals. Each f(n)
// lies below the supremum, which gives one inequality. For the other, a
// simple function s below the supremum is compared, for each 0 < c < 1, with
// the sets where f(n) has passed c·s: they rise and exhaust the points where
// c·s is positive, so the integrals of c·s cut down to them rise to the
// integral of c·s, and each lies below the integral of f(n). Along simple
// functions the theorem computes integrals, and it makes the integral
// additive.

package nonneg_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_simple"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// MonotoneConvergence — the monotone convergence theorem: for a sequence of
// measurable [0, ∞]-valued functions f(n) rising on Ω, the integral of their
// pointwise supremum is the supremum of their integrals. Each f(n) lies below
// the supremum, so its integral lies below that of the supremum. For the
// other bound the section first shows that a simple function u which, at
// every point where it is positive, is strictly passed by some f(n), has
// integral at most the supremum of the integrals: the set where f(n) has
// passed u is measurable, a countable union of level sets of u cut by upper
// rays of f(n); it rises with n; u cut down to it is a simple function below
// f(n), whose integral sums each value z of u times the measure of the part
// of {u = z} passed; and as n grows those parts rise to the level sets where
// z is positive, so the measure follows them. Then for a simple s below the
// supremum and 0 < c < 1, c·s is strictly passed wherever it is positive, so
// c times the integral of s is at most the supremum; every c below 1 doing
// so, the integral of s is too, and so is the integral of the supremum.
var MonotoneConvergence = monotoneConvergenceThm{family.Add(registry.ProofEntry{
	Name: "MonotoneConvergence",
	Key:  "prop_e6dac55e31f33e72",
	Build: family.Sections(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀f:(num → A → extended_nonneg_real).",
		Hypotheses: []string{
			"∀n:num. extended_measurable(Ω, S, f(n))",
			"∀n:num. ∀x:A. x ∈ Ω ⇒ f(n, x) ≤ f(n + 1, x)",
		},
		Conclusion: "nonneg_integral(Ω, S, μ, «limit») = «sup»",
		Abbrev: Abbrev{
			{Name: "limit", Text: "λx:A. extended_sup(image(λn:num. f(n, x), 𝕌))"},
			{Name: "sup", Text: "extended_sup(image(λn:num. nonneg_integral(Ω, S, μ, f(n)), 𝕌))"},
			{Name: "minorants", Text: "{r:extended_nonneg_real | " +
				"    ∃s:(A → real). " +
				"        measure_simple(Ω, S, s) ∧ " +
				"        (∀x:A. x ∈ Ω ⇒ extended_of_real(s(x)) ≤ «limit»(x)) ∧ " +
				"        r = measure_simple_integral(Ω, μ, s)}"},
		},
	}), func(ctx *Script, headline string) *GoalStackNode {
		passedSimple := ctx.Lemma(measure_space.MeasureOn.Statement(Statement{
			Binders: "∀f:(num → A → extended_nonneg_real). ∀u:(A → real).",
			Hypotheses: []string{
				"∀n:num. extended_measurable(Ω, S, f(n))",
				"∀n:num. ∀x:A. x ∈ Ω ⇒ f(n, x) ≤ f(n + 1, x)",
				"measure_simple(Ω, S, u)",
				"∀x:A. x ∈ Ω ∧ &0 < u(x) ⇒ ∃n:num. extended_of_real(u(x)) < f(n, x)",
			},
			Conclusion: "measure_simple_integral(Ω, μ, u) ≤ «sup»",
			Abbrev: Abbrev{
				{Name: "level", Text: "λz:real. {x:A | x ∈ Ω ∧ u(x) = z}"},
				{Name: "passed", Text: "λn:num. {x:A | x ∈ Ω ∧ extended_of_real(u(x)) < f(n, x)}"},
				{Name: "partial", Text: "λn:num. " +
					"    Σ_{z∈image(u, Ω)} extended_of_real(z) * μ(«level»(z) ∩ «passed»(n))"},
			},
		}), func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			measure Fact,
			f *Arrow2[Nat, A, ExtendedNonnegReal],
			u *Arrow[A, Real],
			measurable, rising, simple, reach Fact,
		) {
			sigma := a.Conjuncts(
				a.Unfolded(measure, measure_space.MeasureOn),
				"the measurable sets form a sigma algebra",
				"the empty set has measure zero",
				"countable disjoint unions have the series of their measures")[0]
			unions := a.Conjuncts(
				a.Unfolded(sigma, sigma_algebra.SigmaAlgebraOnDef),
				"every measurable set lies in Ω",
				"Ω is measurable",
				"the complement in Ω of a measurable set is measurable",
				"countable unions of measurable sets are measurable")[3]
			parts := a.Conjuncts(
				a.Unfolded(simple, measure_simple.NonnegSimpleDef),
				"u is measurable",
				"u takes finitely many values on Ω",
				"u is nonnegative on Ω")
			rays := a.Have(
				"every f(n) exceeds each real level on a measurable set",
				"∀n:num. ∀r:real. {x:A | x ∈ Ω ∧ extended_of_real(r) < f(n, x)} ∈ S",
				By(sigma, measurable, measurable_function.ExtendedMeasurableIffRay))
			partsMeasurable := a.Have(
				"the part of a level set of u that f(n) has passed is measurable",
				"∀z:real. ∀n:num. «level»(z) ∩ «passed»(n) ∈ S",
				Derive(func(b *Argument) {
					z := b.FixAs[Real]("z")
					n := b.FixAs[Nat]("n")
					cut := b.Have(
						"on the level set at z, f(n) has passed u where it exceeds z",
						"«level»(z) ∩ «passed»(n) = «level»(z) ∩ {x:A | x ∈ Ω ∧ extended_of_real(z) < f(n, x)}",
						BySets())
					b.Show(
						"a level set of u cut by an upper ray of f(n)",
						By(
							cut,
							sigma,
							simple,
							rays.At(n, z),
							measure_simple.SimpleLevelSets.At(Ω, S, u, z),
							sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
				}))
			_, enumerates := a.ObtainAs[Fun[Nat, Real]](
				"u takes finitely many values on Ω, so a sequence e runs through all of them",
				"∃e:(num → real). image(u, Ω) ⊆ image(e, 𝕌)",
				By(
					parts[1],
					cardinal.FiniteCountable.At(a.TermAs[Set[Real]]("image(u, Ω)")),
					cardinal.CountableCover.At(a.TermAs[Set[Real]]("image(u, Ω)"))))
			passedMeasurable := a.Have(
				"the set where f(n) has passed u is measurable",
				"∀n:num. «passed»(n) ∈ S",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					union := b.Have(
						"it is the union of its parts at the values e(k)",
						"«passed»(n) = ⋃image(λk:num. «level»(e(k)) ∩ «passed»(n), 𝕌)",
						BySets(enumerates))
					pieces := b.Have(
						"each of them measurable",
						"∀k:num. «level»(e(k)) ∩ «passed»(n) ∈ S",
						Derive(func(c *Argument) {
							c.FixAs[Nat]("k")
							c.Show(
								"a part of a level set",
								By(partsMeasurable.At(c.TermAs[Real]("e(k)"), n)))
						}))
					b.Show(
						"a countable union of measurable sets",
						By(union, pieces, unions.At(b.TermAs[Fun2[Nat, A, Bool]]("λk:num. «level»(e(k)) ∩ «passed»(n)"))))
				}))
			passedRising := a.Have(
				"the sets where f(n) has passed u grow with n, f rising",
				"∀n:num. «passed»(n) ⊆ «passed»(n + 1)",
				BySets(rising, extended_nonneg_real.LtIffNotLe, extended_nonneg_real.LeTrans))
			bounded := a.Have(
				"each sum over the values of u of the parts passed "+
					"by f(n) is at most the supremum of the integrals",
				"∀n:num. «partial»(n) ≤ «sup»",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					cut := b.TermAs[Fun[A, Real]]("λx:A. COND(x ∈ «passed»(n), u(x), &0)")
					integral := b.TermAs[ExtendedNonnegReal]("nonneg_integral(Ω, S, μ, f(n))")
					restricted := b.Have(
						"u cut down to where f(n) has passed it is simple, and its integral is that sum",
						"measure_simple(Ω, S, λx:A. COND(x ∈ «passed»(n), u(x), &0)) ∧ "+
							"measure_simple_integral(Ω, μ, λx:A. COND(x ∈ «passed»(n), u(x), &0)) = «partial»(n)",
						By(
							measure,
							simple,
							passedMeasurable.At(n),
							measure_simple.SimpleIntegralRestrict.At(Ω, S, μ, u, b.TermAs[Set[A]]("«passed»(n)"))))
					underneath := b.Have(
						"the cut function lies below f(n) on Ω: u where f(n) has passed it, 0 elsewhere",
						"∀x:A. x ∈ Ω ⇒ extended_of_real(COND(x ∈ «passed»(n), u(x), &0)) ≤ f(n, x)",
						BySets(extended_nonneg_real.ExtendedLtDef, extended_nonneg_real.ZeroLe))
					belowIntegral := b.Have(
						"so its integral is at most the integral of f(n)",
						"«partial»(n) ≤ nonneg_integral(Ω, S, μ, f(n))",
						By(
							restricted,
							underneath,
							measure,
							NonnegIntegralSimple.At(Ω, S, μ, cut),
							NonnegIntegralMono.At(
								Ω,
								S,
								μ,
								b.TermAs[Fun[A, ExtendedNonnegReal]](
									"λx:A. extended_of_real(COND(x ∈ «passed»(n), u(x), &0))"),
								b.TermAs[Fun[A, ExtendedNonnegReal]]("f(n)"))))
					b.Show(
						"and the integral of f(n) is at most the supremum",
						By(
							belowIntegral,
							extended_nonneg_real.SupSequenceUpper.At(
								b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. nonneg_integral(Ω, S, μ, f(n))"),
								n),
							extended_nonneg_real.LeTrans.At(
								b.TermAs[ExtendedNonnegReal]("«partial»(n)"),
								integral,
								b.TermAs[ExtendedNonnegReal]("«sup»"))))
				}))
			levelSup := a.Have(
				"the parts of {u = z} that f(n) has passed rise to the whole level set, and the measure with them",
				Statement{
					Binders:    "∀z:real.",
					Hypotheses: []string{"z ∈ image(u, Ω)"},
					Conclusion: "extended_sup(image(λn:num. extended_of_real(z) * μ(«level»(z) ∩ «passed»(n)), 𝕌)) = " +
						"extended_of_real(z) * μ(«level»(z))",
				},
				Derive(func(b *Argument) {
					z := b.FixAs[Real]("z")
					value := b.Assume()
					zNonneg := b.Have(
						"z is a value of u, so nonnegative",
						"&0 ≤ z",
						By(parts[2], value, set_basic.InImage))
					measures := b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. μ(«level»(z) ∩ «passed»(n))")
					b.Cases(b.Term("z = &0"))
					b.When(
						"at z = 0 both sides are 0",
						func(c *Argument, zero Fact) {
							c.Show(
								"z moves out of the supremum, and 0 times anything is 0",
								By(
									zero,
									zNonneg,
									extended_nonneg_real.SupSequenceScale.At(z, measures),
									extended_nonneg_real.MulComm,
									extended_nonneg_real.MulZero))
						})
					b.Otherwise(
						"off 0 every point of the level set is passed by some f(n)",
						func(c *Argument, nonzero Fact) {
							positive := c.Have(
								"z is positive",
								"&0 < z",
								ByArith(nonzero, zNonneg))
							exhausted := c.Have(
								"so the parts exhaust the level set",
								"⋃image(λn:num. «level»(z) ∩ «passed»(n), 𝕌) = «level»(z)",
								BySets(positive, reach))
							partsRising := c.Have(
								"and rise with n",
								"∀n:num. «level»(z) ∩ «passed»(n) ⊆ «level»(z) ∩ «passed»(n + 1)",
								BySets(passedRising))
							c.Show(
								"the measure is continuous along the rising parts, and z moves out of the supremum",
								By(
									exhausted,
									zNonneg,
									measure,
									partsMeasurable,
									partsRising,
									measure_space.MeasureContinuousIncreasing.At(
										Ω,
										S,
										μ,
										c.TermAs[Fun2[Nat, A, Bool]]("λn:num. «level»(z) ∩ «passed»(n)")),
									extended_nonneg_real.SupSequenceScale.At(z, measures)))
						})
				}))
			termsRising := a.Have(
				"each term z times the measure of the part passed rises with n",
				"∀z:real. ∀n:num. "+
					"    extended_of_real(z) * μ(«level»(z) ∩ «passed»(n)) ≤ "+
					"    extended_of_real(z) * μ(«level»(z) ∩ «passed»(n + 1))",
				Derive(func(b *Argument) {
					z := b.FixAs[Real]("z")
					n := b.FixAs[Nat]("n")
					part := b.TermAs[Set[A]]("«level»(z) ∩ «passed»(n)")
					next := b.TermAs[Set[A]]("«level»(z) ∩ «passed»(n + 1)")
					grows := b.Have(
						"the part passed grows",
						"«level»(z) ∩ «passed»(n) ⊆ «level»(z) ∩ «passed»(n + 1)",
						BySets(passedRising.At(n)))
					b.Show(
						"so does its measure, and z times it",
						By(
							grows,
							measure,
							partsMeasurable.At(z, n),
							partsMeasurable.At(z, b.TermAs[Nat]("n + 1")),
							measure_space.MeasureMono.At(Ω, S, μ, part, next),
							extended_nonneg_real.MulLeMono.At(
								μ.Apply(part),
								μ.Apply(next),
								b.TermAs[ExtendedNonnegReal]("extended_of_real(z)"))))
				}))
			exchanged := a.Have(
				"the supremum of the finite sums is the sum of the suprema, each term rising",
				"extended_sup(image(«partial», 𝕌)) = "+
					"Σ_{z∈image(u, Ω)} extended_sup(image(λn:num. extended_of_real(z) * μ(«level»(z) ∩ «passed»(n)), 𝕌))",
				By(
					parts[1],
					termsRising,
					extended_nonneg_real.SupSequenceSum.At(
						a.TermAs[Fun2[Real, Nat, ExtendedNonnegReal]](
							"λz:real. λn:num. extended_of_real(z) * μ(«level»(z) ∩ «passed»(n))"),
						a.TermAs[Set[Real]]("image(u, Ω)"))))
			collected := a.Have(
				"and each supremum is z times the measure of the whole level set",
				"Σ_{z∈image(u, Ω)} extended_sup(image(λn:num. extended_of_real(z) * μ(«level»(z) ∩ «passed»(n)), 𝕌)) = "+
					"Σ_{z∈image(u, Ω)} extended_of_real(z) * μ(«level»(z))",
				Unfold(extended_nonneg_real.ExtendedSumDef),
				By(levelSup, monoidal.Congruence.Read(extended_nonneg_real.MonoidalAdd)))
			a.Show(
				"the integral of u is the supremum of the sums, each at most the supremum of the integrals",
				By(
					bounded,
					exchanged,
					collected,
					measure_simple.SimpleIntegralDef.At(Ω, μ, u),
					extended_nonneg_real.SupSequenceLeast.At(
						a.TermAs[Fun[Nat, ExtendedNonnegReal]]("«partial»"),
						a.TermAs[ExtendedNonnegReal]("«sup»"))))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			measure Fact,
			f *Arrow2[Nat, A, ExtendedNonnegReal],
			measurable, rising Fact,
		) {
			sup := a.TermAs[ExtendedNonnegReal]("«sup»")
			limitIntegral := a.TermAs[ExtendedNonnegReal]("nonneg_integral(Ω, S, μ, «limit»)")
			sigma := a.Conjuncts(
				a.Unfolded(measure, measure_space.MeasureOn),
				"the measurable sets form a sigma algebra",
				"the empty set has measure zero",
				"countable disjoint unions have the series of their measures")[0]
			termsBelow := a.Have(
				"each f(n) lies below the supremum of the sequence",
				"∀n:num. ∀x:A. f(n, x) ≤ «limit»(x)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.FixAs[A]("x")
					b.Show(
						"a term lies below the supremum of the terms",
						By(extended_nonneg_real.SupSequenceUpper.At(
							b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λm:num. f(m, x)"), n)))
				}))
			lower := a.Have(
				"so each integral of f(n) is at most that of the supremum, and so is their supremum",
				"«sup» ≤ nonneg_integral(Ω, S, μ, «limit»)",
				By(
					termsBelow,
					NonnegIntegralMono,
					extended_nonneg_real.SupSequenceLeast.At(
						a.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. nonneg_integral(Ω, S, μ, f(n))"),
						limitIntegral)))
			scaled := a.Have(
				"for a simple s below the supremum on Ω and 0 < c < 1, c times "+
					"the integral of s is at most the supremum of the integrals",
				Statement{
					Binders: "∀s:(A → real). ∀c:real.",
					Hypotheses: []string{
						"measure_simple(Ω, S, s)",
						"∀x:A. x ∈ Ω ⇒ extended_of_real(s(x)) ≤ «limit»(x)",
						"&0 < c",
						"c < &1",
					},
					Conclusion: "extended_of_real(c) * measure_simple_integral(Ω, μ, s) ≤ «sup»",
				},
				Derive(func(b *Argument) {
					s := b.FixAs[Fun[A, Real]]("s")
					c := b.FixAs[Real]("c")
					given := b.Conjuncts(
						b.Assume(),
						"s is simple",
						"s lies below the supremum on Ω",
						"c is positive",
						"c is below 1")
					cNonneg := b.Have(
						"c is nonnegative",
						"&0 ≤ c",
						ByArith(given[2]))
					scaledSimple := b.Have(
						"c·s is simple",
						"measure_simple(Ω, S, λx:A. c * s(x))",
						By(sigma, given[0], cNonneg, measure_simple.SimpleScale.At(Ω, S, s, c)))
					positivePassed := b.Have(
						"wherever c·s is positive some f(n) passes it, c·s lying strictly below s there",
						"∀x:A. x ∈ Ω ∧ &0 < c * s(x) ⇒ ∃n:num. extended_of_real(c * s(x)) < f(n, x)",
						Derive(func(d *Argument) {
							x := d.FixAs[A]("x")
							point := d.Conjuncts(
								d.Assume(),
								"x lies in Ω",
								"c·s(x) is positive")
							sx := d.TermAs[Real]("s(x)")
							sPositive := d.Have(
								"so is s(x), c being positive",
								"&0 < s(x)",
								ByArith(given[2], point[1]))
							smaller := d.Have(
								"c·s(x) lies strictly below s(x), and so does its image",
								"extended_of_real(c * s(x)) < extended_of_real(s(x))",
								ByArith(
									given[3],
									sPositive,
									real_order_ring.LessThanMulRight.At(c, d.TermAs[Real]("&1"), sx),
									extended_nonneg_real.OfRealLt.At(d.TermAs[Real]("c * s(x)"), sx)))
							belowSup := d.Have(
								"so it lies strictly below the supremum of the f(n, x)",
								"extended_of_real(c * s(x)) < «limit»(x)",
								By(
									smaller,
									point[0],
									given[1].At(x),
									extended_nonneg_real.LtIffNotLe,
									extended_nonneg_real.LeTrans))
							d.Show(
								"and so below one of them",
								By(
									belowSup,
									extended_nonneg_real.SupApprox.At(
										d.TermAs[Set[ExtendedNonnegReal]]("image(λn:num. f(n, x), 𝕌)"),
										d.TermAs[ExtendedNonnegReal]("extended_of_real(c * s(x))")),
									set_basic.InImage,
									set_basic.InUniv))
						}))
					integral := b.Have(
						"so the integral of c·s is at most the supremum of the integrals",
						"measure_simple_integral(Ω, μ, λx:A. c * s(x)) ≤ «sup»",
						By(
							measure,
							measurable,
							rising,
							scaledSimple,
							positivePassed,
							At(passedSimple, Ω, S, μ, f, b.TermAs[Fun[A, Real]]("λx:A. c * s(x)"))))
					b.Show(
						"and that integral is c times the integral of s",
						By(integral, measure, given[0], cNonneg, measure_simple.SimpleIntegralScale.At(Ω, S, μ, s, c)))
				}))
			every := a.Have(
				"so every integral of a simple function below the "+
					"supremum on Ω is at most the supremum of the integrals",
				"∀r:extended_nonneg_real. r ∈ «minorants» ⇒ r ≤ «sup»",
				Derive(func(b *Argument) {
					b.FixAs[ExtendedNonnegReal]("r")
					member := b.Assume()
					s, witnessed := b.UnpackAs[Fun[A, Real]](member, "s")
					pieces := b.Conjuncts(
						witnessed,
						"s is simple",
						"s lies below the supremum on Ω",
						"r is its integral")
					b.Show(
						"c times it is at most the supremum for every c strictly between 0 and 1, so it is",
						By(
							pieces[2],
							pieces[0],
							pieces[1],
							scaled.At(s),
							extended_nonneg_real.LeOfScaledLe.At(
								b.TermAs[ExtendedNonnegReal]("measure_simple_integral(Ω, μ, s)"),
								sup)))
				}))
			a.Show(
				"so the integral of the supremum, the supremum of those integrals, "+
					"is at most the supremum of the integrals too, and the two bounds meet",
				By(
					every,
					lower,
					NonnegIntegralDef.At(Ω, S, μ, a.TermAs[Fun[A, ExtendedNonnegReal]]("«limit»")),
					extended_nonneg_real.SupLeast.At(a.TermAs[Set[ExtendedNonnegReal]]("«minorants»"), sup),
					extended_nonneg_real.LeAntisym.At(limitIntegral, sup)))
		})
	}),
})}

// MonotoneConvergenceSimple — monotone convergence along simple functions:
// for simple functions s(n) rising on Ω, a function g that is their
// pointwise supremum on Ω has as integral the supremum of their simple
// integrals. The embeddings of the s(n) in [0, ∞] are measurable and rise, so
// monotone convergence applies to them; on each the integral is the simple
// integral; and g agrees with their supremum on Ω, which is all the
// integral sees.
var MonotoneConvergenceSimple = monotoneConvergenceSimpleThm{family.Add(registry.ProofEntry{
	Name: "MonotoneConvergenceSimple",
	Key:  "prop_19fbfaccea3baf44",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀s:(num → A → real). ∀g:(A → extended_nonneg_real).",
		Hypotheses: []string{
			"∀n:num. measure_simple(Ω, S, s(n))",
			"∀n:num. ∀x:A. x ∈ Ω ⇒ s(n, x) ≤ s(n + 1, x)",
			"∀x:A. x ∈ Ω ⇒ g(x) = extended_sup(image(λn:num. extended_of_real(s(n, x)), 𝕌))",
		},
		Conclusion: "nonneg_integral(Ω, S, μ, g) = " +
			"extended_sup(image(λn:num. measure_simple_integral(Ω, μ, s(n)), 𝕌))",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		s *Arrow2[Nat, A, Real],
		g *Arrow[A, ExtendedNonnegReal],
		simple, rising, supremum Fact,
	) {
		sigma := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")[0]
		images := a.TermAs[Fun2[Nat, A, ExtendedNonnegReal]]("λn:num. λx:A. extended_of_real(s(n, x))")
		limit := a.TermAs[Fun[A, ExtendedNonnegReal]](
			"λx:A. extended_sup(image(λn:num. extended_of_real(s(n, x)), 𝕌))")
		measurable := a.Have(
			"each s(n), embedded in [0, ∞], is measurable, s(n) being simple",
			"∀n:num. extended_measurable(Ω, S, λx:A. extended_of_real(s(n, x)))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				term := b.TermAs[Fun[A, Real]]("s(n)")
				b.Show(
					"a measurable real function embeds as a measurable one",
					By(
						sigma,
						simple.At(n),
						measure_simple.NonnegSimpleDef.At(Ω, S, term),
						measurable_function.ExtendedMeasurableOfReal.At(Ω, S, term)))
			}))
		imagesRise := a.Have(
			"the embeddings rise on Ω, the s(n) rising there and being nonnegative",
			"∀n:num. ∀x:A. x ∈ Ω ⇒ extended_of_real(s(n, x)) ≤ extended_of_real(s(n + 1, x))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				b.Show(
					"the embedding keeps the order of nonnegative reals",
					By(
						inΩ,
						rising.At(n, x),
						simple.At(b.TermAs[Nat]("n + 1")),
						measure_simple.NonnegSimpleDef.At(Ω, S, b.TermAs[Fun[A, Real]]("s(n + 1)")),
						extended_nonneg_real.OfRealLe.At(b.TermAs[Real]("s(n, x)"), b.TermAs[Real]("s(n + 1, x)"))))
			}))
		same := a.Have(
			"g agrees with the supremum of the embeddings on Ω, so the two integrals agree",
			"nonneg_integral(Ω, S, μ, g) = "+
				"nonneg_integral(Ω, S, μ, λx:A. extended_sup(image(λn:num. extended_of_real(s(n, x)), 𝕌)))",
			By(
				supremum,
				extended_nonneg_real.LeRefl,
				NonnegIntegralMono.At(Ω, S, μ, g, limit),
				NonnegIntegralMono.At(Ω, S, μ, limit, g),
				extended_nonneg_real.LeAntisym))
		integrals := a.Have(
			"on each embedding the integral is the simple integral",
			"∀n:num. "+
				"    nonneg_integral(Ω, S, μ, λx:A. extended_of_real(s(n, x))) = "+
				"    measure_simple_integral(Ω, μ, s(n))",
			By(measure, simple, NonnegIntegralSimple))
		a.Show(
			"monotone convergence along the embeddings",
			By(same, integrals, measure, measurable, imagesRise, MonotoneConvergence.At(Ω, S, μ, images)))
	}),
})}

// NonnegIntegralAdd — the integral adds over sums of measurable [0, ∞]-valued
// functions. f and g are the suprema on Ω of rising sequences s(n) and t(n) of
// simple functions (SimpleApproximation). The sums s(n) + t(n) are simple,
// rise, and have f + g as their supremum, the supremum of a sum of rising
// sequences being the sum of their suprema. Monotone convergence along
// simple functions makes each of the three integrals the supremum of the
// simple integrals along its sequence; the simple integral of s(n) + t(n) is
// the sum of theirs, and those of the s(n) and of the t(n) rise, so the
// supremum of their sums is the sum of their suprema.
var NonnegIntegralAdd = nonnegIntegralAddThm{family.Add(registry.ProofEntry{
	Name: "NonnegIntegralAdd",
	Key:  "prop_8e7963a735929621",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀f g:(A → extended_nonneg_real).",
		Hypotheses: []string{
			"extended_measurable(Ω, S, f)",
			"extended_measurable(Ω, S, g)",
		},
		Conclusion: "nonneg_integral(Ω, S, μ, λx:A. f(x) + g(x)) = " +
			"nonneg_integral(Ω, S, μ, f) + nonneg_integral(Ω, S, μ, g)",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		f, g *Arrow[A, ExtendedNonnegReal],
		fMeasurable, gMeasurable Fact,
	) {
		sigma := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")[0]
		s, sApproximates := a.UnpackAs[Fun2[Nat, A, Real]](
			GroupPremises(sigma, fMeasurable, measure_simple.SimpleApproximation.At(Ω, S, f)), "s")
		sParts := a.Conjuncts(
			sApproximates,
			"each s(n) is simple",
			"the s(n) rise on Ω",
			"they lie below f there",
			"and f is their supremum there")
		t, tApproximates := a.UnpackAs[Fun2[Nat, A, Real]](
			GroupPremises(sigma, gMeasurable, measure_simple.SimpleApproximation.At(Ω, S, g)), "t")
		tParts := a.Conjuncts(
			tApproximates,
			"each t(n) is simple",
			"the t(n) rise on Ω",
			"they lie below g there",
			"and g is their supremum there")
		sumsSimple := a.Have(
			"each s(n) + t(n) is simple",
			"∀n:num. measure_simple(Ω, S, λx:A. s(n, x) + t(n, x))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"a sum of simple functions",
					By(
						sigma,
						sParts[0].At(n),
						tParts[0].At(n),
						measure_simple.SimpleAdd.At(
							Ω, S, b.TermAs[Fun[A, Real]]("s(n)"), b.TermAs[Fun[A, Real]]("t(n)"))))
			}))
		sumsRise := a.Have(
			"the sums rise on Ω",
			"∀n:num. ∀x:A. x ∈ Ω ⇒ s(n, x) + t(n, x) ≤ s(n + 1, x) + t(n + 1, x)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				b.Show(
					"term by term",
					ByArith(inΩ, sParts[1].At(n, x), tParts[1].At(n, x)))
			}))
		sumsSup := a.Have(
			"f + g is their supremum on Ω, the supremum of a "+
				"sum of rising sequences being the sum of the suprema",
			"∀x:A. x ∈ Ω ⇒ f(x) + g(x) = extended_sup(image(λn:num. extended_of_real(s(n, x) + t(n, x)), 𝕌))",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				nonneg := b.Have(
					"the values at x are nonnegative, the s(n) and t(n) being simple",
					"∀n:num. &0 ≤ s(n, x) ∧ &0 ≤ t(n, x)",
					Derive(func(c *Argument) {
						n := c.FixAs[Nat]("n")
						c.Show(
							"a simple function is nonnegative on Ω",
							By(
								inΩ,
								sParts[0].At(n),
								tParts[0].At(n),
								measure_simple.NonnegSimpleDef.At(Ω, S, c.TermAs[Fun[A, Real]]("s(n)")),
								measure_simple.NonnegSimpleDef.At(Ω, S, c.TermAs[Fun[A, Real]]("t(n)"))))
					}))
				split := b.Have(
					"so the embedding adds them",
					"∀n:num. "+
						"    extended_of_real(s(n, x) + t(n, x)) = extended_of_real(s(n, x)) + extended_of_real(t(n, x))",
					Derive(func(c *Argument) {
						n := c.FixAs[Nat]("n")
						c.Show(
							"the images of nonnegative reals add as the reals do",
							By(
								nonneg.At(n),
								extended_nonneg_real.OfRealAdd.At(c.TermAs[Real]("s(n, x)"), c.TermAs[Real]("t(n, x)"))))
					}))
				rise := b.Have(
					"and the embedded values rise",
					"∀n:num. "+
						"    extended_of_real(s(n, x)) ≤ extended_of_real(s(n + 1, x)) ∧ "+
						"    extended_of_real(t(n, x)) ≤ extended_of_real(t(n + 1, x))",
					Derive(func(c *Argument) {
						n := c.FixAs[Nat]("n")
						c.Show(
							"the embedding keeps the order of nonnegative reals",
							By(
								inΩ,
								sParts[1].At(n, x),
								tParts[1].At(n, x),
								nonneg.At(c.TermAs[Nat]("n + 1")),
								extended_nonneg_real.OfRealLe.At(c.TermAs[Real]("s(n, x)"), c.TermAs[Real]("s(n + 1, x)")),
								extended_nonneg_real.OfRealLe.At(c.TermAs[Real]("t(n, x)"), c.TermAs[Real]("t(n + 1, x)"))))
					}))
				b.Show(
					"f(x) and g(x) are the suprema of the two rising sequences",
					By(
						inΩ,
						sParts[3].At(x),
						tParts[3].At(x),
						split,
						rise,
						extended_nonneg_real.SupSequenceAdd.At(
							b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. extended_of_real(s(n, x))"),
							b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. extended_of_real(t(n, x))"))))
			}))
		termwise := a.Have(
			"the simple integral of s(n) + t(n) is the sum of theirs",
			"∀n:num. "+
				"    measure_simple_integral(Ω, μ, λx:A. s(n, x) + t(n, x)) = "+
				"    measure_simple_integral(Ω, μ, s(n)) + measure_simple_integral(Ω, μ, t(n))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"the simple integral is additive",
					By(
						measure,
						sParts[0].At(n),
						tParts[0].At(n),
						measure_simple.SimpleIntegralAdd.At(
							Ω,
							S,
							μ,
							b.TermAs[Fun[A, Real]]("s(n)"),
							b.TermAs[Fun[A, Real]]("t(n)"))))
			}))
		integralsRise := a.Have(
			"the simple integrals of the s(n) rise, and so do those of the t(n)",
			"∀n:num. "+
				"    measure_simple_integral(Ω, μ, s(n)) ≤ measure_simple_integral(Ω, μ, s(n + 1)) ∧ "+
				"    measure_simple_integral(Ω, μ, t(n)) ≤ measure_simple_integral(Ω, μ, t(n + 1))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"s(n) lies below s(n + 1) on Ω, and t(n) below t(n + 1)",
					By(
						measure,
						sParts[0],
						tParts[0],
						sParts[1].At(n),
						tParts[1].At(n),
						measure_simple.SimpleIntegralMono.At(
							Ω,
							S,
							μ,
							b.TermAs[Fun[A, Real]]("s(n)"),
							b.TermAs[Fun[A, Real]]("s(n + 1)")),
						measure_simple.SimpleIntegralMono.At(
							Ω,
							S,
							μ,
							b.TermAs[Fun[A, Real]]("t(n)"),
							b.TermAs[Fun[A, Real]]("t(n + 1)"))))
			}))
		a.Show(
			"the integral of f + g, read along the sums",
			CalcEq(
				Leg(
					a.TermAs[ExtendedNonnegReal](
						"extended_sup(image(λn:num. measure_simple_integral(Ω, μ, λx:A. s(n, x) + t(n, x)), 𝕌))"),
					"monotone convergence along the simple functions s(n) + t(n)",
					By(
						measure,
						sumsSimple,
						sumsRise,
						sumsSup,
						MonotoneConvergenceSimple.At(
							Ω,
							S,
							μ,
							a.TermAs[Fun2[Nat, A, Real]]("λn:num. λx:A. s(n, x) + t(n, x)"),
							a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. f(x) + g(x)")))),
				Leg(
					a.TermAs[ExtendedNonnegReal](
						"extended_sup( "+
							"    image(λn:num. measure_simple_integral(Ω, μ, s(n)) + measure_simple_integral(Ω, μ, t(n)), 𝕌))"),
					"the simple integral of each sum is the sum of the simple integrals",
					Simp(Fwd(termwise))),
				Leg(
					a.TermAs[ExtendedNonnegReal](
						"extended_sup(image(λn:num. measure_simple_integral(Ω, μ, s(n)), 𝕌)) + "+
							"extended_sup(image(λn:num. measure_simple_integral(Ω, μ, t(n)), 𝕌))"),
					"both sequences of simple integrals rise, so the supremum of the sums is the sum of the suprema",
					By(
						integralsRise,
						extended_nonneg_real.SupSequenceAdd.At(
							a.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. measure_simple_integral(Ω, μ, s(n))"),
							a.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. measure_simple_integral(Ω, μ, t(n))")))),
				FinalLeg(
					"monotone convergence along the s(n) and along the t(n)",
					By(
						measure,
						sParts[0],
						sParts[1],
						sParts[3],
						tParts[0],
						tParts[1],
						tParts[3],
						MonotoneConvergenceSimple.At(Ω, S, μ, s, f),
						MonotoneConvergenceSimple.At(Ω, S, μ, t, g)))))
	}),
})}

// NonnegIntegralIndicator — the cut of a height z ∈ [0, ∞] to a measurable
// set E integrates to z times the measure of E. A finite height is the
// embedded value of a simple indicator; an infinite one is the supremum of
// the integer heights, whose cuts rise to it, so monotone convergence gives
// the supremum of their integrals n·μ(E).
var NonnegIntegralIndicator = nonnegIntegralIndicatorThm{family.Add(registry.ProofEntry{
	Name: "NonnegIntegralIndicator",
	Key:  "prop_78d84737dd54b1e0",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders:    "∀E:set(A). ∀z:extended_nonneg_real.",
		Hypotheses: []string{"E ∈ S"},
		Conclusion: "nonneg_integral(Ω, S, μ, λx:A. COND(x ∈ E, z, &0)) = z * μ(E)",
		Abbrev: Abbrev{
			{Name: "indicator", Text: "λc:real. λx:A. COND(x ∈ E, c, &0)"},
			{Name: "cut", Text: "λw:extended_nonneg_real. λx:A. COND(x ∈ E, w, &0)"},
			{Name: "heights", Text: "λn:num. extended_of_real(&n)"},
			{Name: "supHeight", Text: "extended_sup(image(«heights», 𝕌))"},
			{Name: "cuts", Text: "λn:num. «cut»(«heights»(n))"},
			{Name: "integrals", Text: "λn:num. nonneg_integral(Ω, S, μ, «cuts»(n))"},
			{Name: "masses", Text: "λn:num. μ(E) * «heights»(n)"},
		},
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		E *Expr[Set[A]],
		z *Expr[ExtendedNonnegReal],
		event Fact,
	) {
		sigma := a.Have(
			"the measurable sets form a sigma algebra",
			"sigma_algebra_on(Ω, S)",
			By(measure, measure_space.MeasureOn.At(Ω, S, μ)))
		finiteHeights := a.Have(
			"cuts of embedded real heights are measurable and integrate to the scaled mass",
			Statement{
				Binders:    "∀c:real.",
				Hypotheses: []string{"&0 ≤ c"},
				Conclusion: "extended_measurable(Ω, S, «cut»(extended_of_real(c))) ∧ " +
					"nonneg_integral(Ω, S, μ, «cut»(extended_of_real(c))) = μ(E) * extended_of_real(c)",
			},
			Derive(func(b *Argument) {
				c := b.FixAs[Real]("c")
				nonnegative := b.Assume()
				indicator := b.TermAs[Fun[A, Real]]("«indicator»(c)")
				embedding := b.Have(
					"embedding the real indicator gives the cut of the embedded height",
					"(λx:A. extended_of_real(«indicator»(c, x))) = «cut»(extended_of_real(c))",
					CnfRefute())
				b.Show(
					"embed the measurable real indicator and integrate it as a simple function",
					SplitConj(
						Case(
							"the embedding preserves measurability",
							By(
								sigma,
								event,
								embedding,
								measurable_function.RealMeasurableIndicator.At(Ω, S, E, c),
								measurable_function.ExtendedMeasurableOfReal.At(Ω, S, indicator))),
						Case(
							"the simple indicator integral is its height times the mass of E",
							By(
								measure,
								event,
								nonnegative,
								embedding,
								measure_simple.SimpleIntegralIndicator.At(Ω, S, μ, E, c),
								NonnegIntegralSimple.At(Ω, S, μ, indicator),
								extended_nonneg_real.MulComm.At(b.TermAs[ExtendedNonnegReal]("extended_of_real(c)"), μ.Apply(E))))))
			}))
		order := extended_nonneg_real.MulComm.At(z, μ.Apply(E))
		a.Cases(a.Term("z = extended_infinity"))
		a.When(
			"an infinite height is the limit of integer heights",
			func(b *Argument, infinite Fact) {
				heights := b.TermAs[Fun[Nat, ExtendedNonnegReal]]("«heights»")
				heightSup := b.Have(
					"the embedded natural numbers have infinite supremum",
					"«supHeight» = extended_infinity",
					ByContra(),
					Derive(func(c *Argument) {
						finite := c.Hyp("«supHeight» ≠ extended_infinity")
						w := c.TermAs[ExtendedNonnegReal]("«supHeight»")
						value := c.TermAs[Real]("extended_to_real(«supHeight»)")
						bound := c.Have(
							"if the supremum is finite its real value bounds every natural",
							"∀n:num. &n ≤ extended_to_real(«supHeight»)",
							Derive(func(d *Argument) {
								n := d.FixAs[Nat]("n")
								d.Show(
									"read the extended comparison at the finite supremum",
									By(
										finite,
										extended_nonneg_real.SupSequenceUpper.At(heights, n),
										extended_nonneg_real.OfRealToReal.At(w),
										extended_nonneg_real.ToRealNonneg.At(w),
										extended_nonneg_real.OfRealLe.At(d.TermAs[Real]("&n"), value)))
							}))
						one := c.TermAs[Real]("&1")
						positive := c.Have(
							"one is positive",
							"&0 < &1",
							ByArith())
						k, above := c.ObtainAs[Nat](
							"a natural number exceeds the proposed real bound",
							"∃k:num. extended_to_real(«supHeight») < &k * &1",
							By(positive, real_archimedean.Archimedean.At(one, value)))
						c.Show(
							"the two bounds contradict each other",
							ByArith(bound.At(k), above, real_ring.MulRightId.At(c.TermAs[Real]("&k"))))
					}))
				zeroSup := b.Have(
					"the supremum of the constant zero sequence is zero",
					"extended_sup(image(λn:num. extended_of_real(&0), 𝕌)) = &0",
					Derive(func(c *Argument) {
						w := c.TermAs[ExtendedNonnegReal]("extended_sup(image(λn:num. extended_of_real(&0), 𝕌))")
						zero := c.TermAs[ExtendedNonnegReal]("&0")
						c.Show(
							"zero is the least upper bound",
							By(
								extended_nonneg_real.LeRefl.At(zero),
								extended_nonneg_real.ZeroLe.At(w),
								extended_nonneg_real.LeAntisym.At(w, zero),
								extended_nonneg_real.SupSequenceLeast.At(
									c.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. extended_of_real(&0)"), zero)))
					}))
				cutFacts := b.Have(
					"each integer-height cut is measurable with its computed integral",
					"∀n:num. extended_measurable(Ω, S, «cuts»(n)) ∧ «integrals»(n) = «masses»(n)",
					Derive(func(c *Argument) {
						n := c.FixAs[Nat]("n")
						c.Show(
							"the cut at height n is measurable, with integral μ(E)·n",
							By(finiteHeights.At(c.TermAs[Real]("&n")), real_order_ring.NumNonneg.At(n)))
					}))
				measurable := b.Have(
					"all the cuts are measurable",
					"∀n:num. extended_measurable(Ω, S, «cuts»(n))",
					By(cutFacts))
				rising := b.Have(
					"the cuts increase pointwise on the carrier",
					"∀n:num. ∀x:A. x ∈ Ω ⇒ «cuts»(n, x) ≤ «cuts»(n + 1, x)",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("n")
						c.FixAs[A]("x")
						c.Assume()
						c.Cases(c.Term("x ∈ E"))
						c.When(
							"on E the integer heights increase",
							func(d *Argument, on Fact) {
								steps := d.Have(
									"n is at most n + 1",
									"&n ≤ &(n + 1)",
									ByArith())
								d.Show(
									"the embedding is monotone",
									By(on, steps, extended_nonneg_real.OfRealMono.At(d.TermAs[Real]("&n"), d.TermAs[Real]("&(n + 1)"))))
							})
						c.Otherwise(
							"off E the cuts all vanish",
							func(d *Argument, off Fact) {
								d.Show(
									"the value stays zero",
									By(off, extended_nonneg_real.LeRefl.At(d.TermAs[ExtendedNonnegReal]("&0"))))
							})
					}))
				pointwise := b.Have(
					"the integer-height cuts have pointwise supremum the cut of z",
					"«cut»(z) = λx:A. extended_sup(image(λn:num. «cuts»(n, x), 𝕌))",
					Funext(),
					Derive(func(c *Argument) {
						c.FixAs[A]("x")
						c.Cases(c.Term("x ∈ E"))
						c.When(
							"the heights tend to infinity on E",
							func(d *Argument, on Fact) {
								d.Show(
									"the supremum is z",
									By(Normalized, on, infinite, heightSup))
							})
						c.Otherwise(
							"the zero sequence stays zero off E",
							func(d *Argument, off Fact) {
								d.Show(
									"the supremum is zero",
									By(off, zeroSup))
							})
					}))
				integrals := b.Have(
					"the integrals are the products of the heights and the mass of E",
					"«integrals» = «masses»",
					Funext(),
					By(cutFacts))
				convergence := b.Have(
					"monotone convergence gives the supremum of the computed integrals",
					"nonneg_integral(Ω, S, μ, «cut»(z)) = extended_sup(image(«integrals», 𝕌))",
					By(
						measure,
						measurable,
						rising,
						pointwise,
						MonotoneConvergence.At(Ω, S, μ, b.TermAs[Fun2[Nat, A, ExtendedNonnegReal]]("«cuts»"))))
				product := b.Have(
					"multiplication by μ(E) commutes with the supremum of the heights",
					"extended_sup(image(«masses», 𝕌)) = μ(E) * z",
					By(infinite, heightSup, extended_nonneg_real.SupSequenceScaleExtended.At(μ.Apply(E), heights)))
				b.Show(
					"the integral is the infinite height times the mass",
					By(convergence, integrals, product, order))
			})
		a.Otherwise(
			"a finite height is itself an embedded real",
			func(b *Argument, finite Fact) {
				height := b.TermAs[Real]("extended_to_real(z)")
				coefficient := b.Have(
					"the finite height is nonnegative and embeds back to z",
					"extended_of_real(extended_to_real(z)) = z ∧ &0 ≤ extended_to_real(z)",
					By(finite, extended_nonneg_real.ToRealNonneg.At(z), extended_nonneg_real.OfRealToReal.At(z)))
				b.Show(
					"integrate the cut at that height",
					By(coefficient, finiteHeights.At(height), order))
			})
	}),
})}

// NonnegIntegralPushforward — change of variables for the nonnegative
// integral: where ν gives each measurable set of V the μ-mass of its inverse
// image under a measurable F, integrating a measurable k against ν is
// integrating k ∘ F against μ. For a simple k the two level sums agree level
// by level, the levels F misses having empty inverse image; a general k is
// the rising supremum of simple ones, and monotone convergence carries the
// identity to it.
var NonnegIntegralPushforward = nonnegIntegralPushforwardThm{family.Add(registry.ProofEntry{
	Name: "NonnegIntegralPushforward",
	Key:  "prop_91980d7aec288254",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀V:set(B). " +
			"∀T:set(set(B)). " +
			"∀ν:(set(B) → extended_nonneg_real). " +
			"∀F:(A → B). " +
			"∀k:(B → extended_nonneg_real).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"measure_on(V, T, ν)",
			"measurable_map(Ω, S, V, T, F)",
			"∀E:set(B). E ∈ T ⇒ ν(E) = μ(preimage_on(Ω, F, E))",
			"extended_measurable(V, T, k)",
		},
		Conclusion: "nonneg_integral(V, T, ν, k) = nonneg_integral(Ω, S, μ, λx:A. k(F(x)))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		simple := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀V:set(B). " +
				"∀T:set(set(B)). " +
				"∀ν:(set(B) → extended_nonneg_real). " +
				"∀F:(A → B). " +
				"∀s:(B → real).",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"measure_on(V, T, ν)",
				"measurable_map(Ω, S, V, T, F)",
				"∀E:set(B). E ∈ T ⇒ ν(E) = μ(preimage_on(Ω, F, E))",
				"measure_simple(V, T, s)",
			},
			Conclusion: "nonneg_integral(V, T, ν, λy:B. extended_of_real(s(y))) = " +
				"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(s(F(x))))",
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
			V *Expr[Set[B]], T *Expr[Set[Set[B]]], ν *Arrow[Set[B], ExtendedNonnegReal], F *Arrow[A, B],
			s *Arrow[B, Real], measure, targetMeasure, fMeasurable, agreement, sSimple Fact) {
			targetSigma := a.Have(
				"the measurable sets of V form a sigma algebra",
				"sigma_algebra_on(V, T)",
				By(targetMeasure, measure_space.MeasureOn.At(V, T, ν)))
			parts := a.Have(
				"F maps into V and the simple function is measurable, finite-valued, and nonnegative there",
				"image(F, Ω) ⊆ V ∧ real_measurable(V, T, s) ∧ finite(image(s, V)) ∧ (∀y:B. y ∈ V ⇒ &0 ≤ s(y))",
				By(
					fMeasurable,
					sSimple,
					measurable_space.MeasurableMapDef.At(Ω, S, V, T, F),
					measure_simple.NonnegSimpleDef.At(V, T, s)))
			comp := a.TermAs[Fun[A, Real]]("s ∘ F")
			src := a.TermAs[Set[Real]]("image(s ∘ F, Ω)")
			dst := a.TermAs[Set[Real]]("image(s, V)")
			rangeIncluded := a.Have(
				"values attained by the pullback are attained in V",
				"image(s ∘ F, Ω) ⊆ image(s, V)",
				Simp(Fwd(functions.ComposeApply)),
				BySets(parts))
			borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
			line := a.TermAs[Set[Real]]("𝕌")
			measurable := a.Have(
				"composing the two measurable maps gives a measurable observable",
				"real_measurable(Ω, S, s ∘ F)",
				By(
					parts,
					fMeasurable,
					measurable_function.RealMeasurableDef.At(V, T, s),
					measurable_space.MeasurableCompose.At(Ω, S, V, T, line, borel, F, s),
					measurable_function.RealMeasurableDef.At(Ω, S, comp)))
			pullbackNonnegative := a.Have(
				"the pullback is nonnegative wherever F maps into V",
				"∀x:A. x ∈ Ω ⇒ &0 ≤ (s ∘ F)(x)",
				Simp(Fwd(functions.ComposeApply)),
				BySets(parts))
			pulledSimple := a.Have(
				"the pulled-back observable is simple",
				"measure_simple(Ω, S, s ∘ F)",
				By(
					measurable,
					pullbackNonnegative,
					rangeIncluded,
					parts,
					finite_set.FiniteSubset.At(src, dst),
					measure_simple.NonnegSimpleDef.At(Ω, S, comp)))
			level := a.Have(
				"the level set on V pulls back to the level set on Ω",
				"∀r:real. preimage_on(Ω, F, {y:B | y ∈ V ∧ s(y) = r}) = {x:A | x ∈ Ω ∧ (s ∘ F)(x) = r}",
				Simp(Fwd(functions.ComposeApply)),
				BySets(parts))
			q, qDef := a.LetAs[Fun[Real, ExtendedNonnegReal]](
				"q", "λr:real. extended_of_real(r) * μ({x:A | x ∈ Ω ∧ (s ∘ F)(x) = r})")
			_, pDef := a.LetAs[Fun[Real, ExtendedNonnegReal]](
				"p", "λr:real. extended_of_real(r) * ν({y:B | y ∈ V ∧ s(y) = r})")
			weights := a.Have(
				"the two measures assign identical weights to the corresponding levels",
				"p = q",
				Funext(),
				Derive(func(b *Argument) {
					r := b.FixAs[Real]("r")
					levelSet := b.TermAs[Set[B]]("{y:B | y ∈ V ∧ s(y) = r}")
					b.Show(
						"the mass of a measurable level is the mass of its inverse image",
						Simp(Fwd(pDef), Fwd(qDef)),
						By(
							targetSigma,
							sSimple,
							measure_simple.SimpleLevelSets.At(V, T, s, r),
							agreement.At(levelSet),
							level.At(r)))
				}))
			silent := a.Have(
				"additional levels have empty inverse image and contribute zero",
				"∀r:real. r ∈ image(s, V) ∧ r ∉ image(s ∘ F, Ω) ⇒ q(r) = neutral_elem(extended_add)",
				Derive(func(b *Argument) {
					b.FixAs[Real]("r")
					omitted := b.Assume()
					empty := b.Have(
						"the pullback does not attain this level",
						"{x:A | x ∈ Ω ∧ (s ∘ F)(x) = r} = ∅",
						BySets(omitted))
					b.Show(
						"the empty set has zero mass",
						Simp(Fwd(qDef), Fwd(empty)),
						By(
							Normalized,
							measure,
							measure_space.MeasureOn.At(Ω, S, μ),
							extended_nonneg_real.MulZero.At(b.TermAs[ExtendedNonnegReal]("extended_of_real(r)")),
							extended_nonneg_real.NeutralAdd))
				}))
			op := a.TermAs[Fun2[ExtendedNonnegReal, ExtendedNonnegReal, ExtendedNonnegReal]]("extended_add")
			sums := a.Have(
				"enlarging the sum by zero terms does not change it",
				"extended_sum(image(s ∘ F, Ω), q) = extended_sum(image(s, V), q)",
				Simp(Fwd(extended_nonneg_real.ExtendedSumDef)),
				By(rangeIncluded, silent, monoidal.Superset.At(op, src, dst, q)))
			targetIntegral := a.Have(
				"the integral on V is the sum over its levels",
				"nonneg_integral(V, T, ν, λy:B. extended_of_real(s(y))) = extended_sum(image(s, V), p)",
				Simp(Fwd(pDef)),
				By(
					targetMeasure,
					sSimple,
					NonnegIntegralSimple.At(V, T, ν, s),
					measure_simple.SimpleIntegralDef.At(V, ν, s)))
			sourceIntegral := a.Have(
				"the integral on Ω is the sum over the attained pullback levels",
				"nonneg_integral(Ω, S, μ, λx:A. extended_of_real((s ∘ F)(x))) = extended_sum(image(s ∘ F, Ω), q)",
				Simp(Fwd(qDef)),
				By(
					measure,
					pulledSimple,
					NonnegIntegralSimple.At(Ω, S, μ, comp),
					measure_simple.SimpleIntegralDef.At(Ω, μ, comp)))
			a.Show(
				"the level sums coincide",
				CalcEq(
					Leg(
						a.TermAs[ExtendedNonnegReal]("extended_sum(image(s, V), p)"),
						"the integral on V is its level sum",
						By(targetIntegral)),
					Leg(
						a.TermAs[ExtendedNonnegReal]("extended_sum(image(s, V), q)"),
						"corresponding levels carry the same weight",
						Simp(Fwd(weights))),
					Leg(
						a.TermAs[ExtendedNonnegReal]("extended_sum(image(s ∘ F, Ω), q)"),
						"the levels the pullback misses contribute zero",
						By(sums)),
					FinalLeg(
						"the level sum of the pullback is its integral on Ω",
						Simp(Fwd(functions.ComposeApply)),
						By(a.Simplified(sourceIntegral, Fwd(functions.ComposeApply))))))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			V *Expr[Set[B]],
			T *Expr[Set[Set[B]]],
			ν *Arrow[Set[B], ExtendedNonnegReal],
			F *Arrow[A, B],
			k *Arrow[B, ExtendedNonnegReal],
			measure, targetMeasure, fMeasurable, agreement, kMeasurable Fact,
		) {
			targetSigma := a.Have(
				"the measurable sets of V form a sigma algebra",
				"sigma_algebra_on(V, T)",
				By(targetMeasure, measure_space.MeasureOn.At(V, T, ν)))
			_, chosen := a.UnpackAs[Fun2[Nat, B, Real]](
				GroupPremises(targetSigma, kMeasurable, measure_simple.SimpleApproximation.At(V, T, k)), "s")
			approximation := a.Conjuncts(
				chosen,
				"each approximant is simple",
				"the approximants increase",
				"the embedded approximants are below k",
				"their pointwise supremum is k")
			into := a.Have(
				"the map F sends points of Ω into V",
				"∀x:A. x ∈ Ω ⇒ F(x) ∈ V",
				BySets(fMeasurable, measurable_space.MeasurableMapDef.At(Ω, S, V, T, F)))
			g, gDef := a.LetAs[Fun2[Nat, B, ExtendedNonnegReal]]("g", "λn:num. λy:B. extended_of_real(s(n, y))")
			f, fDef := a.LetAs[Fun2[Nat, A, ExtendedNonnegReal]](
				"f", "λn:num. λx:A. extended_of_real(s(n, F(x)))")
			measurable := a.Have(
				"the approximants and their pullbacks are measurable",
				"∀n:num. extended_measurable(V, T, g(n)) ∧ extended_measurable(Ω, S, f(n))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					sn := b.TermAs[Fun[B, Real]]("s(n)")
					gn := b.TermAs[Fun[B, ExtendedNonnegReal]]("g(n)")
					fn := b.TermAs[Fun[A, ExtendedNonnegReal]]("f(n)")
					gnMeasurable := b.Have(
						"a nonnegative simple measurable real function embeds measurably",
						"extended_measurable(V, T, g(n))",
						By(
							Normalized,
							targetSigma,
							gDef,
							approximation[0].At(n),
							measure_simple.NonnegSimpleDef.At(V, T, sn),
							measurable_function.ExtendedMeasurableOfReal.At(V, T, sn)))
					composite := b.Have(
						"the source approximant is the composite with F",
						"f(n) = g(n) ∘ F",
						By(fDef, gDef, functions.ComposeApply.At(gn, F)))
					b.Show(
						"composition preserves measurability",
						By(
							Normalized,
							fMeasurable,
							gnMeasurable,
							composite,
							measurable_function.ExtendedMeasurableDef.At(V, T, gn),
							measurable_function.ExtendedMeasurableDef.At(Ω, S, fn),
							measurable_space.MeasurableCompose.At(Ω, S, V, T,
								b.TermAs[Set[ExtendedNonnegReal]]("𝕌"),
								b.TermAs[Set[Set[ExtendedNonnegReal]]]("extended_borel"), F, gn)))
				}))
			gRises := a.Have(
				"the embedded approximants on V increase",
				"∀n:num. ∀y:B. y ∈ V ⇒ g(n, y) ≤ g(n + 1, y)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					y := b.FixAs[B]("y")
					member := b.Assume()
					b.Show(
						"the embedding preserves the pointwise order",
						By(
							Normalized,
							member,
							approximation[1].At(n, y),
							gDef,
							extended_nonneg_real.OfRealMono.At(b.TermAs[Real]("s(n, y)"), b.TermAs[Real]("s(n + 1, y)"))))
				}))
			fRises := a.Have(
				"the embedded approximants on Ω increase after composition",
				"∀n:num. ∀x:A. x ∈ Ω ⇒ f(n, x) ≤ f(n + 1, x)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					x := b.FixAs[A]("x")
					member := b.Assume()
					b.Show(
						"the point F(x) belongs to V, where the approximants are increasing",
						By(
							Normalized,
							member,
							into.At(x),
							approximation[1].At(n, F.Apply(x)),
							fDef,
							extended_nonneg_real.OfRealMono.At(
								b.TermAs[Real]("s(n, F(x))"), b.TermAs[Real]("s(n + 1, F(x))"))))
				}))
			gLimit := a.Have(
				"the approximants on V have pointwise supremum k",
				"∀y:B. y ∈ V ⇒ k(y) = extended_sup(image(λn:num. g(n, y), 𝕌))",
				Simp(Fwd(gDef)),
				By(approximation[3]))
			fLimit := a.Have(
				"the pulled-back approximants have supremum k at F(x)",
				"∀x:A. x ∈ Ω ⇒ k(F(x)) = extended_sup(image(λn:num. f(n, x), 𝕌))",
				Simp(Fwd(fDef)),
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					member := b.Assume()
					b.Show(
						"take the pointwise supremum at the image point",
						By(member, into.At(x), approximation[3].At(F.Apply(x))))
				}))
			gIntegral := a.Have(
				"monotone convergence gives the integral on V",
				"nonneg_integral(V, T, ν, k) = extended_sup(image(λn:num. nonneg_integral(V, T, ν, g(n)), 𝕌))",
				By(
					targetMeasure,
					targetSigma,
					measurable,
					gRises,
					gLimit,
					MonotoneConvergence.At(V, T, ν, g),
					NonnegIntegralEqOn.At(V, T, ν, k,
						a.TermAs[Fun[B, ExtendedNonnegReal]]("λy:B. extended_sup(image(λn:num. g(n, y), 𝕌))"))))
			fIntegral := a.Have(
				"monotone convergence gives the integral on Ω",
				"nonneg_integral(Ω, S, μ, λx:A. k(F(x))) = "+
					"extended_sup(image(λn:num. nonneg_integral(Ω, S, μ, f(n)), 𝕌))",
				By(
					measure,
					measurable,
					fRises,
					fLimit,
					MonotoneConvergence.At(Ω, S, μ, f),
					NonnegIntegralEqOn.At(
						Ω,
						S,
						μ,
						a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. k(F(x))"),
						a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_sup(image(λn:num. f(n, x), 𝕌))"))))
			sameIntegrals := a.Have(
				"the approximation integrals coincide term by term",
				"(λn:num. nonneg_integral(V, T, ν, g(n))) = (λn:num. nonneg_integral(Ω, S, μ, f(n)))",
				Funext(),
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Show(
						"each term is the pushforward identity for a simple function",
						Simp(Fwd(gDef), Fwd(fDef)),
						By(
							measure,
							targetMeasure,
							fMeasurable,
							agreement,
							approximation[0].At(n),
							At(simple, Ω, S, μ, V, T, ν, F, b.TermAs[Fun[B, Real]]("s(n)"))))
				}))
			a.Show(
				"the two limits are suprema of the same sequence",
				By(a.Simplified(gIntegral, Fwd(sameIntegrals)), fIntegral))
		})
	}),
})}
