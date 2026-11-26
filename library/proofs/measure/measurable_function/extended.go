// extended.go — measurable functions with values in [0, ∞]. Measurability
// for extended_borel is decided by the rays above real levels, which
// generate it; through them the embedding of a measurable real function
// and the pointwise supremum and infimum of a measurable sequence are
// measurable, and a measurable function reaches each real level on a
// measurable set.

package measurable_function

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// ExtendedMeasurableIffRay — a [0, ∞]-valued function is measurable
// exactly when the set where it exceeds each real level is measurable.
// The rays above real levels generate extended_borel: each is a Borel set,
// so a measurable function pulls it back into S, and a function pulling
// every generator back into S is measurable for the σ-algebra they
// generate.
var ExtendedMeasurableIffRay = extendedMeasurableIffRayThm{family.Add(registry.ProofEntry{
	Name: "ExtendedMeasurableIffRay",
	Key:  "prop_e9f6bb97766cf475",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → extended_nonneg_real).",
		Hypotheses: []string{"sigma_algebra_on(Ω, S)"},
		Conclusion: "extended_measurable(Ω, S, f) ⇔ " +
			"∀r:real. {x:A | x ∈ Ω ∧ extended_of_real(r) < f(x)} ∈ S",
		Abbrev: Abbrev{
			{Name: "rays", Text: "{E:set(extended_nonneg_real) | " +
				"    ∃r:real. E = {y:extended_nonneg_real | extended_of_real(r) < y}}"},
		},
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		f *Arrow[A, ExtendedNonnegReal],
		sigma Fact,
	) {
		a.Iff()
		a.Forward(
			"a measurable f pulls each ray, a Borel set of [0, ∞], back into S",
			func(b *Argument, measurable Fact) {
				b.FixAs[Real]("r")
				generator := b.Have(
					"the ray above r is one of the generating rays",
					"{y:extended_nonneg_real | extended_of_real(r) < y} ∈ «rays»",
					BySets())
				borelRay := b.Have(
					"so it lies in every σ-algebra they generate",
					"{y:extended_nonneg_real | extended_of_real(r) < y} ∈ extended_borel",
					Simp(Fwd(ExtendedBorelDef), Fwd(sigma_algebra.GeneratedSigmaDef)),
					BySets(generator))
				ray := b.Have(
					"its preimage is the set where f exceeds r",
					"preimage_on(Ω, f, {y:extended_nonneg_real | extended_of_real(r) < y}) = "+
						"{x:A | x ∈ Ω ∧ extended_of_real(r) < f(x)}",
					BySets())
				maps := b.Unfolded(measurable, ExtendedMeasurableDef)
				preimages := b.Unfolded(maps, measurable_space.MeasurableMapDef)
				b.Show(
					"Borel preimages are measurable",
					By(preimages, borelRay, ray))
			})
		a.Backward(
			"measurable rays of f are the preimages of the generators, which decide measurability",
			func(b *Argument, rays Fact) {
				generators := b.Have(
					"each generating ray pulls back to a ray of f",
					"∀t:set(extended_nonneg_real). t ∈ «rays» ⇒ preimage_on(Ω, f, t) ∈ S",
					Derive(func(d *Argument) {
						d.FixAs[Set[ExtendedNonnegReal]]("t")
						generator := d.Assume()
						r, shape := d.ObtainAs[Real](
							"t is the ray above some real r",
							"∃r:real. t = {y:extended_nonneg_real | extended_of_real(r) < y}",
							BySets(generator))
						preimage := d.Have(
							"its preimage is the set where f exceeds r",
							"preimage_on(Ω, f, t) = {x:A | x ∈ Ω ∧ extended_of_real(r) < f(x)}",
							BySets(shape))
						d.Show(
							"which is measurable",
							By(rays.At(r), preimage))
					}))
				bounds := b.Have(
					"the rays are sets of [0, ∞], where f takes its values",
					"«rays» ⊆ {t:set(extended_nonneg_real) | t ⊆ 𝕌} ∧ image(f, Ω) ⊆ 𝕌",
					BySets())
				b.Show(
					"so f is measurable for the σ-algebra the rays generate",
					Simp(Fwd(ExtendedMeasurableDef), Fwd(ExtendedBorelDef)),
					By(
						generators,
						sigma,
						bounds,
						measurable_space.MeasurableGenerated.At(
							Ω,
							S,
							b.TermAs[Set[ExtendedNonnegReal]]("𝕌"),
							b.TermAs[Set[Set[ExtendedNonnegReal]]]("«rays»"),
							f)))
			})
	}),
})}

// ExtendedMeasurableOfReal — a measurable real function, embedded in
// [0, ∞], is measurable. The embedding clamps at 0, so its image exceeds
// the image of r exactly where f exceeds r and is positive: the ray is
// the intersection of two rays of f.
var ExtendedMeasurableOfReal = extendedMeasurableOfRealThm{family.Add(registry.ProofEntry{
	Name: "ExtendedMeasurableOfReal",
	Key:  "prop_79c3c371eaa4c941",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"real_measurable(Ω, S, f)",
		},
		Conclusion: "extended_measurable(Ω, S, λx:A. extended_of_real(f(x)))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		f *Arrow[A, Real],
		sigma, measurable Fact,
	) {
		realRays := a.Have(
			"the rays of f are measurable",
			"∀t:real. {x:A | x ∈ Ω ∧ t < f(x)} ∈ S",
			By(sigma, measurable, RealMeasurableIffRay.At(Ω, S, f)))
		rays := a.Have(
			"so are the rays of its embedding",
			"∀r:real. {x:A | x ∈ Ω ∧ extended_of_real(r) < extended_of_real(f(x))} ∈ S",
			Derive(func(b *Argument) {
				b.FixAs[Real]("r")
				clamp := b.Have(
					"the embedding of f exceeds the image of r where f exceeds both r and 0",
					"{x:A | x ∈ Ω ∧ extended_of_real(r) < extended_of_real(f(x))} = "+
						"{x:A | x ∈ Ω ∧ r < f(x)} ∩ {x:A | x ∈ Ω ∧ &0 < f(x)}",
					BySets(extended_nonneg_real.OfRealLt))
				b.Show(
					"an intersection of two measurable sets is measurable",
					By(realRays, clamp, sigma, sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
			}))
		a.Show(
			"upper rays decide measurability",
			By(
				sigma,
				rays,
				ExtendedMeasurableIffRay.At(
					Ω, S, a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(f(x))"))))
	}),
})}

// ExtendedMeasurableToReal gives the real reading of an extended measurable
// function. A nonnegative threshold excludes the infinity set, where
// extended_to_real takes value zero. A negative threshold gives the carrier.
var ExtendedMeasurableToReal = extendedMeasurableToRealThm{family.Add(registry.ProofEntry{
	Name: "ExtendedMeasurableToReal",
	Key:  "prop_e5517ac5cfea13ba",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀g:(A → extended_nonneg_real).",
		Hypotheses: []string{"sigma_algebra_on(Ω, S)", "extended_measurable(Ω, S, g)"},
		Conclusion: "real_measurable(Ω, S, λx:A. extended_to_real(g(x)))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		g *Arrow[A, ExtendedNonnegReal],
		sigma, measurable Fact,
	) {
		rays := a.Have(
			"the extended function's upper rays are measurable",
			"∀r:real. {x:A | x ∈ Ω ∧ extended_of_real(r) < g(x)} ∈ S",
			By(sigma, measurable, ExtendedMeasurableIffRay.At(Ω, S, g)))
		closure := sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)
		infinityEvent := a.Have(
			"the set on which the extended value is infinite is measurable",
			"{x:A | x ∈ Ω ∧ g(x) = extended_infinity} ∈ S",
			By(sigma, measurable, ExtendedMeasurableInfinitySet.At(Ω, S, g)))
		realRays := a.Have(
			"the finite-valued reading has measurable real upper rays",
			"∀t:real. {x:A | x ∈ Ω ∧ t < extended_to_real(g(x))} ∈ S",
			Derive(func(b *Argument) {
				t := b.FixAs[Real]("t")
				b.Cases(b.Term("t < &0"))
				b.When(
					"a negative threshold gives the whole carrier",
					func(c *Argument, negative Fact) {
						all := c.Have(
							"every real value supplied by extended_to_real exceeds the threshold",
							"∀x:A. t < extended_to_real(g(x))",
							ByArith(negative, extended_nonneg_real.ToRealNonneg))
						whole := c.Have(
							"every point of Ω belongs to the ray",
							"{x:A | x ∈ Ω ∧ t < extended_to_real(g(x))} = Ω",
							BySets(all))
						c.Show(
							"the carrier is measurable",
							By(sigma, closure, whole))
					})
				b.Otherwise(
					"a nonnegative threshold excludes the infinity set",
					func(c *Argument, nonnegative Fact) {
						comparison := c.Have(
							"above the threshold means finite with extended value above the embedded threshold",
							"∀y:extended_nonneg_real. "+
								"    t < extended_to_real(y) ⇔ extended_of_real(t) < y ∧ y ≠ extended_infinity",
							Derive(func(d *Argument) {
								y := d.FixAs[ExtendedNonnegReal]("y")
								d.Cases(d.Term("y = extended_infinity"))
								d.When(
									"infinity reads as zero",
									func(e *Argument, atInfinity Fact) {
										e.Show(
											"zero does not exceed the threshold",
											ByArith(nonnegative, atInfinity, extended_nonneg_real.ToRealInfinity))
									})
								d.Otherwise(
									"a finite value embeds back as itself",
									func(e *Argument, finite Fact) {
										value := e.TermAs[Real]("extended_to_real(y)")
										embedded := e.Have(
											"compare the embedded threshold to the embedded finite value",
											"extended_of_real(t) < y ⇔ t < extended_to_real(y) ∧ &0 < extended_to_real(y)",
											By(finite, extended_nonneg_real.OfRealToReal.At(y), extended_nonneg_real.OfRealLt.At(t, value)))
										positive := e.Have(
											"a value above a nonnegative threshold is positive",
											"t < extended_to_real(y) ⇒ &0 < extended_to_real(y)",
											ByArith(nonnegative))
										e.Show(
											"above the threshold is the same in both readings",
											By(Normalized, finite, embedded, positive))
									})
							}))
						difference := c.Have(
							"the real ray removes the infinity set from the extended ray",
							"{x:A | x ∈ Ω ∧ t < extended_to_real(g(x))} = "+
								"{x:A | x ∈ Ω ∧ extended_of_real(t) < g(x)} ∖ {x:A | x ∈ Ω ∧ g(x) = extended_infinity}",
							BySets(comparison))
						c.Show(
							"measurable events are closed under difference",
							By(sigma, rays.At(t), infinityEvent, difference, sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
					})
			}))
		a.Show(
			"measurability follows from the real upper rays",
			By(
				sigma,
				realRays,
				RealMeasurableIffRay.At(Ω, S,
					a.TermAs[Fun[A, Real]]("λx:A. extended_to_real(g(x))"))))
	}),
})}

// ExtendedMeasurableOnEvent — a measurable [0, ∞]-valued function cut to 0
// off a measurable set E stays measurable: no level lies below 0, so the
// cut exceeds a level exactly on the part inside E of the set where f does.
var ExtendedMeasurableOnEvent = extendedMeasurableOnEventThm{family.Add(registry.ProofEntry{
	Name: "ExtendedMeasurableOnEvent",
	Key:  "prop_a18352205a08c476",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀E:set(A). ∀f:(A → extended_nonneg_real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"E ∈ S",
			"extended_measurable(Ω, S, f)",
		},
		Conclusion: "extended_measurable(Ω, S, λx:A. COND(x ∈ E, f(x), &0))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		E *Expr[Set[A]],
		f *Arrow[A, ExtendedNonnegReal],
		sigma, event, measurable Fact,
	) {
		rays := a.Have(
			"every strict upper level set of the cut is measurable",
			"∀r:real. {x:A | x ∈ Ω ∧ extended_of_real(r) < COND(x ∈ E, f(x), &0)} ∈ S",
			Derive(func(b *Argument) {
				b.FixAs[Real]("r")
				threshold := b.TermAs[ExtendedNonnegReal]("extended_of_real(r)")
				zero := b.TermAs[ExtendedNonnegReal]("extended_of_real(&0)")
				cutRay := b.Have(
					"off E the cut is 0, and no extended_of_real(r) lies below 0, so a "+
						"strict upper level set of the cut is the corresponding level set inside E",
					"{x:A | x ∈ Ω ∧ extended_of_real(r) < COND(x ∈ E, f(x), &0)} = "+
						"E ∩ {x:A | x ∈ Ω ∧ extended_of_real(r) < f(x)}",
					BySets(
						extended_nonneg_real.LtIffNotLe.At(threshold, zero),
						extended_nonneg_real.ZeroLe.At(threshold)))
				originalRay := b.Have(
					"the original level set is measurable",
					"{x:A | x ∈ Ω ∧ extended_of_real(r) < f(x)} ∈ S",
					By(sigma, measurable, ExtendedMeasurableIffRay.At(Ω, S, f)))
				b.Show(
					"intersect the level set with the measurable event",
					By(cutRay, event, originalRay, sigma, sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
			}))
		a.Show(
			"the level sets establish measurability",
			By(sigma, rays, ExtendedMeasurableIffRay))
	}),
})}

// ExtendedMeasurableInfinitySet — a measurable [0, ∞]-valued function is ∞
// on a measurable set: a value is ∞ exactly when it exceeds every natural
// number, so the set is what Ω keeps of the rays at the natural numbers.
var ExtendedMeasurableInfinitySet = extendedMeasurableInfinitySetThm{family.Add(registry.ProofEntry{
	Name: "ExtendedMeasurableInfinitySet",
	Key:  "prop_b80870d522ff2420",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀g:(A → extended_nonneg_real).",
		Hypotheses: []string{"sigma_algebra_on(Ω, S)", "extended_measurable(Ω, S, g)"},
		Conclusion: "{x:A | x ∈ Ω ∧ g(x) = extended_infinity} ∈ S",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		g *Arrow[A, ExtendedNonnegReal],
		sigma, measurable Fact,
	) {
		rays := a.Have(
			"the extended function's upper rays are measurable",
			"∀r:real. {x:A | x ∈ Ω ∧ extended_of_real(r) < g(x)} ∈ S",
			By(sigma, measurable, ExtendedMeasurableIffRay.At(Ω, S, g)))
		asIntersection := a.Have(
			"the infinity set is what remains after removing all finite upper bounds",
			"{x:A | x ∈ Ω ∧ g(x) = extended_infinity} = "+
				"Ω ∖ ⋃image(λn:num. Ω ∖ {x:A | x ∈ Ω ∧ extended_of_real(&n) < g(x)}, 𝕌)",
			BySets(extended_nonneg_real.EqInfinityIffAboveNaturals))
		closure := sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)
		complements := a.Have(
			"the complement of each ray at a natural number is measurable in Ω",
			"∀n:num. Ω ∖ {x:A | x ∈ Ω ∧ extended_of_real(&n) < g(x)} ∈ S",
			By(sigma, closure, rays))
		a.Show(
			"a complement of a countable union of measurable sets",
			By(sigma, closure, complements, asIntersection))
	}),
})}

// ExtendedMeasurableSup — the pointwise supremum of a sequence of
// measurable [0, ∞]-valued functions is measurable. A real level lies
// below the supremum exactly where it lies below some term, so the ray of
// the supremum is the countable union of the rays of the terms.
var ExtendedMeasurableSup = extendedMeasurableSupThm{family.Add(registry.ProofEntry{
	Name: "ExtendedMeasurableSup",
	Key:  "prop_19ec910c30541f1d",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(num → A → extended_nonneg_real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"∀n:num. extended_measurable(Ω, S, f(n))",
		},
		Conclusion: "extended_measurable(Ω, S, λx:A. extended_sup(image(λn:num. f(n, x), 𝕌)))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		f *Arrow2[Nat, A, ExtendedNonnegReal],
		sigma, measurable Fact,
	) {
		termRays := a.Have(
			"every term has measurable rays",
			"∀n:num. ∀r:real. {x:A | x ∈ Ω ∧ extended_of_real(r) < f(n, x)} ∈ S",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"upper rays decide the measurability of f(n)",
					By(
						measurable.At(n),
						sigma,
						ExtendedMeasurableIffRay.At(Ω, S, b.TermAs[Fun[A, ExtendedNonnegReal]]("f(n)"))))
			}))
		pointwise := a.Have(
			"a real level lies below the supremum exactly where it lies below some term",
			"∀r:real. ∀x:A. "+
				"    extended_of_real(r) < extended_sup(image(λn:num. f(n, x), 𝕌)) ⇔ "+
				"    ∃n:num. extended_of_real(r) < f(n, x)",
			Derive(func(b *Argument) {
				b.FixAs[Real]("r")
				b.FixAs[A]("x")
				terms := b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. f(n, x)")
				b.Show(
					"the supremum lies at or below the level exactly when every term does",
					By(
						extended_nonneg_real.LtIffNotLe,
						extended_nonneg_real.SupSequenceLeast.At(
							terms,
							b.TermAs[ExtendedNonnegReal]("extended_of_real(r)")),
						At(extended_nonneg_real.SupSequenceUpper, terms),
						extended_nonneg_real.LeTrans))
			}))
		union := a.Have(
			"so the ray of the supremum is the union of the rays of the terms",
			"∀r:real. "+
				"    {x:A | x ∈ Ω ∧ extended_of_real(r) < extended_sup(image(λn:num. f(n, x), 𝕌))} = "+
				"    ⋃image(λn:num. {x:A | x ∈ Ω ∧ extended_of_real(r) < f(n, x)}, 𝕌)",
			BySets(pointwise))
		rays := a.Have(
			"which is measurable, a countable union of measurable sets",
			"∀r:real. {x:A | x ∈ Ω ∧ extended_of_real(r) < extended_sup(image(λn:num. f(n, x), 𝕌))} ∈ S",
			Derive(func(b *Argument) {
				r := b.FixAs[Real]("r")
				b.Do(union.At(r).Rw())
				b.Show(
					"countable unions are measurable",
					By(termRays, sigma, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
			}))
		a.Show(
			"upper rays decide measurability",
			By(
				sigma,
				rays,
				ExtendedMeasurableIffRay.At(
					Ω,
					S,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_sup(image(λn:num. f(n, x), 𝕌))"))))
	}),
})}

// ExtendedMeasurableInf — the pointwise infimum of a sequence of measurable
// [0, ∞]-valued functions is measurable. A level r ≥ 0 lies strictly below
// the infimum exactly where some r + 1/(m + 1) lies strictly below every
// term: a finite infimum lies a whole 1/(m + 1) above r for some m, and it
// lies below each term. So the ray of the infimum above r is the countable
// union over m of the sets where every term exceeds r + 1/(m + 1), each the
// complement of a countable union of complements of rays of the terms. A
// negative level embeds as 0, so its ray is the ray above 0.
var ExtendedMeasurableInf = extendedMeasurableInfThm{family.Add(registry.ProofEntry{
	Name: "ExtendedMeasurableInf",
	Key:  "prop_c37a65f156300630",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(num → A → extended_nonneg_real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"∀n:num. extended_measurable(Ω, S, f(n))",
		},
		Conclusion: "extended_measurable(Ω, S, «infimum»)",
		Abbrev: Abbrev{
			{Name: "infimum", Text: "λx:A. extended_inf(image(λn:num. f(n, x), 𝕌))"},
		},
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		f *Arrow2[Nat, A, ExtendedNonnegReal],
		sigma, measurable Fact,
	) {
		closure := a.Conjuncts(
			a.Unfolded(sigma, sigma_algebra.SigmaAlgebraOnDef),
			"every measurable set lies in Ω",
			"Ω is measurable",
			"the complement in Ω of a measurable set is measurable",
			"countable unions of measurable sets are measurable")
		complements, unions := closure[2], closure[3]
		termRays := a.Have(
			"every term exceeds each real level on a measurable set",
			"∀n:num. ∀r:real. {x:A | x ∈ Ω ∧ extended_of_real(r) < f(n, x)} ∈ S",
			By(sigma, measurable, ExtendedMeasurableIffRay))
		allAbove := a.Have(
			"so does the set where every term exceeds a level",
			"∀q:real. {x:A | x ∈ Ω ∧ ∀n:num. extended_of_real(q) < f(n, x)} ∈ S",
			Derive(func(b *Argument) {
				q := b.FixAs[Real]("q")
				complement := b.Have(
					"it is the complement of the union of the complements of the rays of the terms",
					"{x:A | x ∈ Ω ∧ ∀n:num. extended_of_real(q) < f(n, x)} = "+
						"Ω ∖ ⋃image(λn:num. Ω ∖ {x:A | x ∈ Ω ∧ extended_of_real(q) < f(n, x)}, 𝕌)",
					BySets())
				outside := b.Have(
					"the complement of each ray is measurable",
					"∀n:num. Ω ∖ {x:A | x ∈ Ω ∧ extended_of_real(q) < f(n, x)} ∈ S",
					Derive(func(c *Argument) {
						n := c.FixAs[Nat]("n")
						c.Show(
							"the complement of a measurable set",
							By(
								termRays.At(n, q),
								complements.At(c.TermAs[Set[A]]("{x:A | x ∈ Ω ∧ extended_of_real(q) < f(n, x)}"))))
					}))
				b.Show(
					"the complement of a countable union of measurable sets",
					By(
						complement,
						outside,
						unions.At(b.TermAs[Fun2[Nat, A, Bool]](
							"λn:num. Ω ∖ {x:A | x ∈ Ω ∧ extended_of_real(q) < f(n, x)}")),
						complements.At(b.TermAs[Set[A]](
							"⋃image(λn:num. Ω ∖ {x:A | x ∈ Ω ∧ extended_of_real(q) < f(n, x)}, 𝕌)"))))
			}))
		pointwise := a.Have(
			"a level r ≥ 0 lies below the infimum exactly where some r + 1/(m + 1) lies below every term",
			Statement{
				Binders:    "∀r:real. ∀x:A.",
				Hypotheses: []string{"&0 ≤ r"},
				Conclusion: "extended_of_real(r) < «infimum»(x) ⇔ " +
					"∃m:num. ∀n:num. extended_of_real(r + real_inv(&m + &1)) < f(n, x)",
			},
			Derive(func(b *Argument) {
				r := b.FixAs[Real]("r")
				b.FixAs[A]("x")
				nonneg := b.Assume()
				infimum := b.TermAs[ExtendedNonnegReal]("«infimum»(x)")
				lowered := b.TermAs[ExtendedNonnegReal]("extended_of_real(r)")
				terms := b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. f(n, x)")
				b.Iff()
				b.Forward(
					"the infimum lies a whole 1/(m + 1) above r for some m, and below every term",
					func(c *Argument, below Fact) {
						lower := c.Have(
							"the infimum lies below every term",
							"∀n:num. «infimum»(x) ≤ f(n, x)",
							Derive(func(d *Argument) {
								n := d.FixAs[Nat]("n")
								d.Show(
									"each term is one of the values",
									By(
										extended_nonneg_real.InfLower.At(
											d.TermAs[Set[ExtendedNonnegReal]]("image(λn:num. f(n, x), 𝕌)"),
											d.TermAs[ExtendedNonnegReal]("f(n, x)")),
										set_image.FunInRange.At(terms, n)))
							}))
						near := c.Have(
							"some r + 1/(m + 1) lies below the infimum",
							"∃m:num. extended_of_real(r + real_inv(&m + &1)) < «infimum»(x)",
							Derive(func(d *Argument) {
								d.Cases(d.Term("«infimum»(x) = extended_infinity"))
								d.When(
									"an infinite infimum lies above every real",
									func(e *Argument, infinite Fact) {
										e.Take(e.TermAs[Nat]("0"))
										e.Show(
											"the image of a real is finite",
											By(
												infinite,
												extended_nonneg_real.ExtendedLtDef,
												extended_nonneg_real.LeInfinity,
												extended_nonneg_real.OfRealNotInfinity))
									})
								d.Otherwise(
									"a finite infimum t lies above r, and some 1/(m + 1) fits below t − r",
									func(e *Argument, finite Fact) {
										value := e.TermAs[Real]("extended_to_real(«infimum»(x))")
										gap := e.Have(
											"r lies below t, the image of t being the infimum",
											"r < extended_to_real(«infimum»(x))",
											By(
												finite,
												below,
												extended_nonneg_real.OfRealToReal.At(infimum),
												extended_nonneg_real.OfRealLt.At(r, value)))
										m, small := e.ObtainAs[Nat](
											"some 1/(m + 1) lies below t − r",
											"∃m:num. real_inv(&m + &1) < extended_to_real(«infimum»(x)) - r",
											ByArith(
												gap,
												real_archimedean.ExistsReciprocalBelow.At(
													e.TermAs[Real]("extended_to_real(«infimum»(x)) - r"))))
										e.Take(m)
										e.Show(
											"r + 1/(m + 1) lies below t, a positive real",
											ByArith(
												finite,
												nonneg,
												gap,
												small,
												extended_nonneg_real.OfRealToReal.At(infimum),
												extended_nonneg_real.OfRealLt.At(e.TermAs[Real]("r + real_inv(&m + &1)"), value)))
									})
							}))
						m, level := c.UnpackAs[Nat](near, "m")
						c.Take(m)
						n := c.FixAs[Nat]("n")
						c.Show(
							"it lies below the infimum, hence below f(n, x)",
							By(level, lower.At(n), extended_nonneg_real.LtIffNotLe, extended_nonneg_real.LeTrans))
					})
				b.Backward(
					"r + 1/(m + 1) lies below every term, so at or below the infimum, and r strictly below it",
					func(c *Argument, some Fact) {
						_, every := c.UnpackAs[Nat](some, "m")
						level := c.TermAs[ExtendedNonnegReal]("extended_of_real(r + real_inv(&m + &1))")
						step := c.Have(
							"1/(m + 1) is positive",
							"&0 < real_inv(&m + &1)",
							ByArith())
						atMost := c.Have(
							"r + 1/(m + 1) lies at or below the infimum",
							"extended_of_real(r + real_inv(&m + &1)) ≤ «infimum»(x)",
							By(
								every,
								extended_nonneg_real.ExtendedLtDef,
								extended_nonneg_real.InfSequenceGreatest.At(terms, level)))
						c.Show(
							"and r lies strictly below r + 1/(m + 1), a positive real",
							ByArith(
								atMost,
								nonneg,
								step,
								extended_nonneg_real.OfRealLt.At(r, c.TermAs[Real]("r + real_inv(&m + &1)")),
								extended_nonneg_real.LtIffNotLe.At(lowered, infimum),
								extended_nonneg_real.LtIffNotLe.At(lowered, level),
								extended_nonneg_real.LeTrans.At(level, infimum, lowered)))
					})
			}))
		nonnegRays := a.Have(
			"the infimum exceeds a level r ≥ 0 on a measurable set",
			"∀r:real. &0 ≤ r ⇒ {x:A | x ∈ Ω ∧ extended_of_real(r) < «infimum»(x)} ∈ S",
			Derive(func(b *Argument) {
				r := b.FixAs[Real]("r")
				nonneg := b.Assume()
				union := b.Have(
					"it is the union over m of the sets where every term exceeds r + 1/(m + 1)",
					"{x:A | x ∈ Ω ∧ extended_of_real(r) < «infimum»(x)} = "+
						"⋃image(λm:num. {x:A | x ∈ Ω ∧ ∀n:num. extended_of_real(r + real_inv(&m + &1)) < f(n, x)}, 𝕌)",
					BySets(pointwise.At(r), nonneg))
				pieces := b.Have(
					"each of them measurable",
					"∀m:num. {x:A | x ∈ Ω ∧ ∀n:num. extended_of_real(r + real_inv(&m + &1)) < f(n, x)} ∈ S",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("m")
						c.Show(
							"every term exceeds the level r + 1/(m + 1) there",
							By(allAbove.At(c.TermAs[Real]("r + real_inv(&m + &1)"))))
					}))
				b.Show(
					"a countable union of measurable sets",
					By(
						union,
						pieces,
						unions.At(b.TermAs[Fun2[Nat, A, Bool]](
							"λm:num. {x:A | x ∈ Ω ∧ ∀n:num. extended_of_real(r + real_inv(&m + &1)) < f(n, x)}"))))
			}))
		rays := a.Have(
			"so it exceeds any level on a measurable set, a negative level embedding as 0",
			"∀r:real. {x:A | x ∈ Ω ∧ extended_of_real(r) < «infimum»(x)} ∈ S",
			Derive(func(b *Argument) {
				r := b.FixAs[Real]("r")
				b.Cases(b.Term("&0 ≤ r"))
				b.When(
					"a level r ≥ 0",
					func(c *Argument, nonneg Fact) {
						c.Show(
							"as just shown",
							By(nonneg, nonnegRays.At(r)))
					})
				b.Otherwise(
					"a negative level embeds as 0, so its ray is the ray above 0",
					func(c *Argument, negative Fact) {
						c.Show(
							"the ray above 0 is measurable",
							ByArith(negative, nonnegRays.At(c.TermAs[Real]("&0")), extended_nonneg_real.OfRealNeg.At(r)))
					})
			}))
		a.Show(
			"upper rays decide measurability",
			By(
				sigma,
				rays,
				ExtendedMeasurableIffRay.At(Ω, S, a.TermAs[Fun[A, ExtendedNonnegReal]]("«infimum»"))))
	}),
})}

// ExtendedMeasurableAtLeast — where a measurable [0, ∞]-valued function
// reaches a real level is a measurable set. At a level r > 0, a value lies
// below r exactly when it is at most r − 1/(n + 1) for some n, so the set is
// what Ω keeps once the complements of the rays at the levels
// r − 1/(n + 1) are removed. At a level r ≤ 0 the image of r is 0, which f
// reaches everywhere.
var ExtendedMeasurableAtLeast = extendedMeasurableAtLeastThm{family.Add(registry.ProofEntry{
	Name: "ExtendedMeasurableAtLeast",
	Key:  "prop_e83a8b0f88b83f31",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → extended_nonneg_real). ∀r:real.",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"extended_measurable(Ω, S, f)",
		},
		Conclusion: "{x:A | x ∈ Ω ∧ extended_of_real(r) ≤ f(x)} ∈ S",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		f *Arrow[A, ExtendedNonnegReal],
		r *Expr[Real],
		sigma, measurable Fact,
	) {
		closure := a.Unfolded(sigma, sigma_algebra.SigmaAlgebraOnDef)
		rays := a.Have(
			"f pulls back every ray above a real level into S",
			"∀q:real. {x:A | x ∈ Ω ∧ extended_of_real(q) < f(x)} ∈ S",
			By(sigma, measurable, ExtendedMeasurableIffRay.At(Ω, S, f)))
		a.Cases(a.Term("&0 < r"))
		a.When(
			"at a positive level f reaches r exactly where it is at most no r − 1/(n + 1)",
			func(b *Argument, positive Fact) {
				approach := b.Have(
					"a value lies below r exactly when it is at most r − 1/(n + 1) for some n",
					"∀y:extended_nonneg_real. "+
						"    y < extended_of_real(r) ⇔ ∃n:num. y ≤ extended_of_real(r - real_inv(&n + &1))",
					Derive(func(c *Argument) {
						y := c.FixAs[ExtendedNonnegReal]("y")
						c.Iff()
						c.Forward(
							"a value y below r is a real v < r, and r − v exceeds some 1/(n + 1)",
							func(d *Argument, below Fact) {
								_, value := d.ObtainAs[Real](
									"y lies below r, so it is not ∞: it is a real v ≥ 0",
									"∃v:real. &0 ≤ v ∧ y = extended_of_real(v)",
									By(
										below,
										extended_nonneg_real.ExtendedCases.At(y),
										extended_nonneg_real.LeInfinity,
										extended_nonneg_real.LtIffNotLe))
								gap := d.Have(
									"v lies below r",
									"v < r",
									By(Normalized, below, value, extended_nonneg_real.OfRealLt))
								n, small := d.ObtainAs[Nat](
									"r − v exceeds some 1/(n + 1)",
									"∃n:num. real_inv(&n + &1) < r - v",
									ByArith(gap, real_archimedean.ExistsReciprocalBelow.At(d.TermAs[Real]("r - v"))))
								d.Take(n)
								shifted := d.Have(
									"so v is at most r − 1/(n + 1), which is nonnegative",
									"v ≤ r - real_inv(&n + &1) ∧ &0 ≤ r - real_inv(&n + &1)",
									ByArith(small, value))
								d.Show(
									"and y is at most the image of r − 1/(n + 1)",
									By(value, shifted, extended_nonneg_real.OfRealLe))
							})
						c.Backward(
							"r − 1/(n + 1) lies below r",
							func(d *Argument, some Fact) {
								_, atMost := d.UnpackAs[Nat](some, "n")
								inverse := d.Have(
									"1/(n + 1) is positive",
									"&0 < real_inv(&n + &1)",
									ByArith(real_order_field.InvPos.At(d.TermAs[Real]("&n + &1"))))
								shifted := d.Have(
									"so r − 1/(n + 1) lies below r",
									"r - real_inv(&n + &1) < r",
									ByArith(inverse))
								d.Show(
									"and y, at most it, lies below r",
									By(
										atMost,
										positive,
										shifted,
										extended_nonneg_real.OfRealLt,
										extended_nonneg_real.LtIffNotLe,
										extended_nonneg_real.LeTrans))
							})
					}))
				short := b.Have(
					"what each ray of f at r − 1/(n + 1) leaves of Ω is measurable",
					"∀n:num. Ω ∖ {x:A | x ∈ Ω ∧ extended_of_real(r - real_inv(&n + &1)) < f(x)} ∈ S",
					By(closure, rays))
				complement := b.Have(
					"f reaches r exactly where it lies in none of those",
					"{x:A | x ∈ Ω ∧ extended_of_real(r) ≤ f(x)} = "+
						"Ω ∖ ⋃image(λn:num. Ω ∖ {x:A | x ∈ Ω ∧ extended_of_real(r - real_inv(&n + &1)) < f(x)}, 𝕌)",
					BySets(approach, extended_nonneg_real.LtIffNotLe))
				b.Show(
					"so the set is measurable",
					By(complement, closure, short))
			})
		a.Otherwise(
			"at a level r ≤ 0 the image of r is 0, which f reaches everywhere",
			func(b *Argument, notPositive Fact) {
				nonpositive := b.Have(
					"r is at most 0",
					"r ≤ &0",
					ByArith(notPositive))
				whole := b.Have(
					"so the set is Ω",
					"{x:A | x ∈ Ω ∧ extended_of_real(r) ≤ f(x)} = Ω",
					BySets(nonpositive, extended_nonneg_real.OfRealNeg, extended_nonneg_real.ZeroLe))
				b.Show(
					"which is measurable",
					By(whole, closure))
			})
	}),
})}
