// distribution_function.go — the distribution function of a Borel probability on the line: it
// determines the probability, it is continuous from the right, and it is continuous from the left
// at a point of no mass.

package random_variable

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/borel_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/proofs/topology/borel_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ProbabilityDeterminedByLowerRays — a Borel probability on the line is
// determined by its distribution function. The complements of the lower rays
// are the upper rays, on which the two laws then agree too; the upper rays
// are closed under intersection and generate the Borel sets, and two
// probabilities agreeing on a generating π-system agree on every set it
// generates.
var ProbabilityDeterminedByLowerRays = probabilityDeterminedByLowerRaysThm{family.Add(registry.ProofEntry{
	Name: "ProbabilityDeterminedByLowerRays",
	Key:  "prop_9a7a98ec6945a16",
	Build: family.Sections(Statement{
		Binders: "∀μ ν:(set(real) → extended_nonneg_real). ∀E:set(real).",
		Hypotheses: []string{
			"probability_on(𝕌, borel_sets(real_topology), μ)",
			"probability_on(𝕌, borel_sets(real_topology), ν)",
			"∀b:real. μ({x:real | x ≤ b}) = ν({x:real | x ≤ b})",
			"E ∈ borel_sets(real_topology)",
		},
		Conclusion: "μ(E) = ν(E)",
		Abbrev: Abbrev{
			{Name: "upperRays", Text: "image(λc:real. {x:real | c < x}, 𝕌)"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			intersectionOfRays := ctx.Lemma("∀c d:real. "+
				"    {x:real | c < x} ∩ {x:real | d < x} = {x:real | max(c, d) < x}",
				func(a *Argument, c, d *Expr[Real]) {
					a.Show(
						"a point exceeds both thresholds exactly when it exceeds their maximum",
						Simp(Fwd(set_basic.Extension)),
						Derive(func(b *Argument) {
							b.FixAs[Real]("x")
							both := b.Have(
								"both lower bounds are equivalent to their maximum",
								"c < x ∧ d < x ⇔ max(c, d) < x",
								ByArith())
							b.Show(
								"read the intersection pointwise",
								BySets(both))
						}))
				})
			rayPiSystem := ctx.Lemma("pi_system_on(𝕌, «upperRays»)",
				func(a *Argument) {
					line := a.TermAs[Set[Real]]("𝕌")
					a.Show(
						"the upper rays are sets of reals closed under intersection",
						Simp(Fwd(sigma_algebra.PiSystemDef)),
						SplitConj(
							Case(
								"each ray is a subset of the real carrier",
								BySets(),
							),
							Case(
								"the intersection of two rays is the ray at the larger threshold",
								Derive(func(e *Argument) {
									e.FixAs[Set[Real]]("s")
									e.FixAs[Set[Real]]("t")
									rays := e.Assume()
									c, d, thresholds := e.Obtain2As[Real, Real](
										"each of the two sets is a ray",
										"∃c d:real. s = {x:real | c < x} ∧ t = {x:real | d < x}",
										BySets(rays))
									meet := e.Have(
										"their intersection is the ray at the maximum",
										"s ∩ t = {x:real | max(c, d) < x}",
										By(thresholds, At(intersectionOfRays, c, d)))
									e.Show(
										"and that ray is an upper ray",
										By(
											meet,
											set_image.FunInImage.At(
												e.TermAs[Fun2[Real, Real, Bool]]("λc:real. {x:real | c < x}"),
												line,
												e.TermAs[Real]("max(c, d)")),
											set_basic.InUniv.Inst[Real]()))
								}),
							)))
				})
			raysGenerateBorel := ctx.Lemma("borel_sets(real_topology) = generated_sigma(𝕌, «upperRays»)",
				func(a *Argument) {
					line := a.TermAs[Set[Real]]("𝕌")
					borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
					topology := a.TermAs[Set[Set[Real]]]("real_topology")
					rays := a.TermAs[Set[Set[Real]]]("«upperRays»")
					generated := a.TermAs[Set[Set[Real]]]("generated_sigma(𝕌, «upperRays»)")
					ray := a.TermAs[Fun2[Real, Real, Bool]]("λc:real. {x:real | c < x}")
					identity := a.TermAs[Fun[Real, Real]]("λx:real. x")
					raySets := a.Have(
						"the upper rays are sets of reals",
						"«upperRays» ⊆ {E:set(real) | E ⊆ 𝕌}",
						BySets())
					generatedSigma := a.Have(
						"they generate a σ-algebra on the line that holds them",
						"sigma_algebra_on(𝕌, generated_sigma(𝕌, «upperRays»)) ∧ "+
							"«upperRays» ⊆ generated_sigma(𝕌, «upperRays»)",
						By(raySets, sigma_algebra.GeneratedSigmaAlgebra.At(line, rays)))
					raysOpen := a.Have(
						"the upper rays are open",
						"«upperRays» ⊆ real_topology",
						By(real_topology.RayAboveOpen, set_image.ImageSubsetIff.At(ray, line, topology)))
					borelSigma := a.Have(
						"the Borel sets form a σ-algebra on the line holding its open sets",
						"sigma_algebra_on(𝕌, borel_sets(real_topology)) ∧ real_topology ⊆ borel_sets(real_topology)",
						By(borel_space.BorelSigmaAlgebra.At(topology), real_topology.RealSpace))
					generatedInBorel := a.Have(
						"so the σ-algebra the rays generate lies in the Borel sets",
						"generated_sigma(𝕌, «upperRays») ⊆ borel_sets(real_topology)",
						By(
							raysOpen,
							borelSigma,
							set_order.SubsetTrans.At(rays, topology, borel),
							sigma_algebra.GeneratedSigmaLeast.At(line, rays, borel)))
					raysGenerated := a.Have(
						"every upper ray of the line lies in the generated σ-algebra",
						"∀c:real. {x:real | x ∈ 𝕌 ∧ c < x} ∈ generated_sigma(𝕌, «upperRays»)",
						Simp(Fwd(set_basic.InUniv)),
						Derive(func(b *Argument) {
							c := b.FixAs[Real]("c")
							b.Show(
								"the ray at c is an upper ray",
								By(
									generatedSigma,
									set_image.FunInImage.At(ray, line, c),
									set_basic.InUniv.At(c),
									set_basic.SubsetDef.At(rays, generated)))
						}))
					identityMeasurable := a.Have(
						"so the identity is measurable from the generated σ-algebra to the Borel sets",
						"measurable_map(𝕌, generated_sigma(𝕌, «upperRays»), 𝕌, borel_sets(real_topology), λx:real. x)",
						By(
							raysGenerated,
							generatedSigma,
							measurable_function.RealMeasurableIffRay.At(line, generated, identity),
							measurable_function.RealMeasurableDef.At(line, generated, identity)))
					borelInGenerated := a.Have(
						"so every Borel set lies in the generated σ-algebra",
						"borel_sets(real_topology) ⊆ generated_sigma(𝕌, «upperRays»)",
						Simp(Fwd(set_basic.SubsetDef)),
						Derive(func(b *Argument) {
							b.FixAs[Set[Real]]("B")
							bBorel := b.Assume()
							preimage := b.Have(
								"the preimage of B under the identity is B",
								"preimage_on(𝕌, λx:real. x, B) = B",
								BySets())
							b.Show(
								"the identity carries B back into the generated σ-algebra",
								By(
									preimage,
									bBorel,
									identityMeasurable,
									measurable_space.MeasurableMapDef.At(line, generated, line, borel, identity)))
						}))
					a.Show(
						"the two σ-algebras contain each other",
						By(borelInGenerated, generatedInBorel, set_order.SubsetAntisym.At(borel, generated)))
				})
			complementMass := ctx.Lemma(Statement{
				Binders: "∀Ω:set(real). " +
					"∀S:set(set(real)). " +
					"∀μ ν:(set(real) → extended_nonneg_real). " +
					"∀E:set(real).",
				Hypotheses: []string{
					"probability_on(Ω, S, μ)",
					"probability_on(Ω, S, ν)",
					"E ∈ S",
					"μ(E) = ν(E)",
				},
				Conclusion: "μ(Ω ∖ E) = ν(Ω ∖ E)",
			},
				func(
					a *Argument,
					Ω *Expr[Set[Real]],
					S *Expr[Set[Set[Real]]],
					μ, ν *Arrow[Set[Real], ExtendedNonnegReal],
					E *Expr[Set[Real]],
					μProbability, νProbability, eIn, agree Fact,
				) {
					one := a.TermAs[ExtendedNonnegReal]("extended_of_real(&1)")
					complementE := a.TermAs[Set[Real]]("Ω ∖ E")
					bounds := a.Have(
						"each law splits the total mass one at E",
						"μ(Ω ∖ E) + μ(E) = extended_of_real(&1) ∧ ν(Ω ∖ E) + μ(E) = extended_of_real(&1)",
						By(
							Normalized,
							μProbability,
							νProbability,
							eIn,
							agree,
							probability_space.ProbabilityBounds.At(Ω, S, μ, E),
							probability_space.ProbabilityBounds.At(Ω, S, ν, E)))
					finite := a.Have(
						"the mass of E, an event of a probability, is finite",
						"μ(E) ≠ extended_infinity",
						By(μProbability, eIn, probability_space.ProbabilityEventFinite.At(Ω, S, μ, E)))
					a.Show(
						"cancel the finite mass of E from the two splittings",
						By(
							finite,
							bounds,
							extended_nonneg_real.LeRefl.At(one),
							extended_nonneg_real.AddLeCancel.At(μ.Apply(complementE), ν.Apply(complementE), μ.Apply(E)),
							extended_nonneg_real.AddLeCancel.At(ν.Apply(complementE), μ.Apply(complementE), μ.Apply(E)),
							extended_nonneg_real.LeAntisym.At(μ.Apply(complementE), ν.Apply(complementE))))
				})
			return ctx.Theorem(headline,
				func(
					a *Argument,
					μ, ν *Arrow[Set[Real], ExtendedNonnegReal],
					E *Expr[Set[Real]],
					μProbability, νProbability, lowerRays, eBorel Fact,
				) {
					line := a.TermAs[Set[Real]]("𝕌")
					borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
					upperRays := a.Have(
						"the two laws agree on every upper ray, the complement of a lower ray",
						"∀b:real. μ({x:real | b < x}) = ν({x:real | b < x})",
						Derive(func(c *Argument) {
							b := c.FixAs[Real]("b")
							complement := c.Have(
								"the open upper ray complements the closed lower ray",
								"𝕌 ∖ {x:real | x ≤ b} = {x:real | b < x}",
								Simp(Fwd(set_basic.Extension)),
								c.ForEach(func(x *Expr[Real]) Action { return BySets(real_order_ring.NotLessEq.At(b, x)) }))
							c.Show(
								"subtract equal lower-ray masses from the common total",
								By(
									lowerRays,
									complement,
									μProbability,
									νProbability,
									borel_function.RaysBorel.At(b),
									At(complementMass, line, borel, μ, ν, c.TermAs[Set[Real]]("{x:real | x ≤ b}"))))
						}))
					onRays := a.Have(
						"so they agree on the π-system of upper rays",
						"∀R:set(real). R ∈ «upperRays» ⇒ μ(R) = ν(R)",
						Derive(func(c *Argument) {
							c.FixAs[Set[Real]]("R")
							ray := c.Assume()
							b, isRay := c.ObtainAs[Real](
								"R is the upper ray at some b",
								"∃b:real. R = {x:real | b < x}",
								BySets(ray))
							c.Show(
								"the two laws agree on that ray",
								By(upperRays.At(b), isRay))
						}))
					a.Show(
						"probabilities agreeing on a generating π-system agree on every set it generates",
						By(
							onRays,
							eBorel,
							μProbability,
							νProbability,
							rayPiSystem,
							raysGenerateBorel,
							probability_space.ProbabilityOnDef.At(line, borel, μ),
							probability_space.ProbabilityOnDef.At(line, borel, ν),
							extended_nonneg_real.OfRealNotInfinity.At(a.TermAs[Real]("&1")),
							measure_space.MeasureDeterminedByPi.At(
								line, a.TermAs[Set[Set[Real]]]("«upperRays»"), borel, μ, ν, E)))
				})
		}),
})}

// continuityFromAbove — continuity from above for a Borel probability on the line, read in real
// masses: when Borel sets decrease to a set of mass r, some set of the sequence has mass below
// r + e. The first set has finite mass, so the mass of the meet is the infimum of the masses, and
// an infimum below r + e is approached by a mass below it.
var continuityFromAbove = continuityFromAboveThm{family.Add(registry.ProofEntry{
	Name: "continuityFromAbove",
	Key:  "prop_d9b573a497dbabe4",
	Build: family.Theorem(Statement{
		Binders: "∀μ:(set(real) → extended_nonneg_real). ∀E:(num → set(real)). ∀r e:real.",
		Hypotheses: []string{
			"probability_on(𝕌, borel_sets(real_topology), μ)",
			"∀k:num. E(k) ∈ borel_sets(real_topology)",
			"∀k:num. E(k + 1) ⊆ E(k)",
			"μ(⋂image(E, 𝕌)) = extended_of_real(r)",
			"&0 ≤ r",
			"&0 < e",
		},
		Conclusion: "∃k:num. extended_to_real(μ(E(k))) < r + e",
	},
		func(
			a *Argument,
			μ *Arrow[Set[Real], ExtendedNonnegReal],
			E *Arrow2[Nat, Real, Bool],
			r, e *Expr[Real],
			probability, borel, decreasing, meet, nonneg, pos Fact,
		) {
			line := a.TermAs[Set[Real]]("𝕌")
			borelSets := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
			finite := a.Have(
				"the first set has finite mass",
				"μ(E(0)) ≠ extended_infinity",
				By(
					probability,
					borel.At(a.TermAs[Nat]("0")),
					probability_space.ProbabilityEventFinite.At(line, borelSets, μ, a.TermAs[Set[Real]]("E(0)"))),
			)
			infimum := a.Have(
				"so the mass of the meet is the infimum of the masses",
				"μ(⋂image(E, 𝕌)) = extended_inf(image(λk:num. μ(E(k)), 𝕌))",
				By(
					probability,
					probability_space.ProbabilityOnDef.At(line, borelSets, μ),
					borel,
					decreasing,
					finite,
					measure_space.MeasureContinuousDecreasing.At(line, borelSets, μ, E)),
			)
			margin := a.Have(
				"r lies below r + e, which is positive",
				"r < r + e ∧ &0 < r + e",
				ByArith(nonneg, pos),
			)
			below := a.Have(
				"so the infimum lies below r + e",
				"extended_inf(image(λk:num. μ(E(k)), 𝕌)) < extended_of_real(r + e)",
				By(Normalized, margin, infimum, meet, extended_nonneg_real.OfRealLt.At(r, a.TermAs[Real]("r + e"))),
			)
			m, approach := a.ObtainAs[ExtendedNonnegReal](
				"and so does some mass of the sequence",
				"∃m:extended_nonneg_real. m ∈ image(λk:num. μ(E(k)), 𝕌) ∧ m < extended_of_real(r + e)",
				By(
					below,
					extended_nonneg_real.InfApprox.At(
						a.TermAs[Set[ExtendedNonnegReal]]("image(λk:num. μ(E(k)), 𝕌)"),
						a.TermAs[ExtendedNonnegReal]("extended_of_real(r + e)"))),
			)
			k, index := a.ObtainAs[Nat](
				"the mass of some E(k)",
				"∃k:num. m = μ(E(k))",
				By(
					approach,
					set_basic.InImage.At(
						a.TermAs[Fun[Nat, ExtendedNonnegReal]]("λk:num. μ(E(k))"), a.TermAs[Set[Nat]]("𝕌"), m)),
			)
			a.Show(
				"whose real value, the mass being finite, lies below r + e",
				Witness(k),
				By(
					probability,
					borel.At(k),
					index,
					approach,
					probability_space.ProbabilityEventFinite.At(line, borelSets, μ, a.TermAs[Set[Real]]("E(k)")),
					extended_nonneg_real.OfRealLt.At(
						a.TermAs[Real]("extended_to_real(μ(E(k)))"), a.TermAs[Real]("r + e"))),
			)
		}),
})}

// DistributionFunctionRightContinuous — the distribution function of a Borel probability on the
// line is continuous from the right: the half-lines {y ≤ t + 1/(k + 1)} decrease to the one at t,
// so by continuity from above one of them has mass within e of the mass at t. Stated as some
// b > t with F(b) within e of F(t), it is continuity: F is increasing, so every point of (t, b]
// is within e too.
var DistributionFunctionRightContinuous = distributionFunctionRightContinuousThm{family.Add(registry.ProofEntry{
	Name: "DistributionFunctionRightContinuous",
	Key:  "prop_f6a4348dd5222e3f",
	Build: family.Sections(Statement{
		Binders: "∀μ:(set(real) → extended_nonneg_real). ∀t e:real.",
		Hypotheses: []string{
			"probability_on(𝕌, borel_sets(real_topology), μ)",
			"&0 < e",
		},
		Conclusion: "∃b:real. " +
			"    t < b ∧ extended_to_real(μ({y:real | y ≤ b})) < extended_to_real(μ({y:real | y ≤ t})) + e",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			reciprocalMeet := ctx.Lemma("∀t y:real. (∀k:num. y ≤ t + real_inv(&k + &1)) ⇔ y ≤ t",
				func(a *Argument, t, y *Expr[Real]) {
					a.Iff()
					a.Forward(
						"a point below t + 1/(k + 1) for every k is below t, the reciprocals falling below any gap",
						func(b *Argument, all Fact) {
							beyond := b.SupposeNot()
							gap := b.Have(
								"otherwise y − t is positive",
								"&0 < y - t",
								ByArith(beyond),
							)
							n, small := b.ObtainAs[Nat](
								"so some 1/(n + 1) lies below it",
								"∃n:num. real_inv(&n + &1) < y - t",
								By(gap, real_archimedean.ExistsReciprocalBelow.At(b.TermAs[Real]("y - t"))),
							)
							b.Show(
								"against y ≤ t + 1/(n + 1)",
								ByArith(all.At(n), small),
							)
						})
					a.Backward(
						"a point below t is below t + 1/(k + 1), the reciprocal being positive",
						func(b *Argument, below Fact) {
							b.FixAs[Nat]("k")
							positive := b.Have(
								"1/(k + 1) is positive",
								"&0 < real_inv(&k + &1)",
								ByArith(),
							)
							b.Show(
								"so y ≤ t + 1/(k + 1)",
								ByArith(below, positive),
							)
						})
				})

			return ctx.Theorem(headline,
				func(
					a *Argument,
					μ *Arrow[Set[Real], ExtendedNonnegReal],
					t, e *Expr[Real],
					probability, pos Fact,
				) {
					line := a.TermAs[Set[Real]]("𝕌")
					borelSets := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
					rays := a.Have(
						"the half-lines {y ≤ t + 1/(k + 1)} are Borel sets",
						"∀k:num. {y:real | y ≤ t + real_inv(&k + &1)} ∈ borel_sets(real_topology)",
						By(borel_function.RaysBorel),
					)
					decreasing := a.Have(
						"they decrease, as the reciprocals do",
						"∀k:num. {y:real | y ≤ t + real_inv(&(k + 1) + &1)} ⊆ {y:real | y ≤ t + real_inv(&k + &1)}",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("k")
							b.Show(
								"1/(k + 2) ≤ 1/(k + 1)",
								ByArith(
									real_order_field.InvAntitoneWeak.At(b.TermAs[Real]("&k + &1"), b.TermAs[Real]("&(k + 1) + &1")),
									set_basic.SubsetDef),
							)
						}),
					)
					meet := a.Have(
						"and meet in the half-line at t",
						"⋂image(λk:num. {y:real | y ≤ t + real_inv(&k + &1)}, 𝕌) = {y:real | y ≤ t}",
						Simp(Fwd(set_image.IntersImage)),
						BySets(At(reciprocalMeet, t)),
					)
					_, near := a.ObtainAs[Nat](
						"so some half-line right of t has mass within e of the one at t",
						"∃k:num. "+
							"    extended_to_real(μ({y:real | y ≤ t + real_inv(&k + &1)})) < "+
							"    extended_to_real(μ({y:real | y ≤ t})) + e",
						By(
							probability,
							rays,
							decreasing,
							pos,
							meet,
							borel_function.RaysBorel.At(t),
							probability_space.ProbabilityEventFinite.At(
								line, borelSets, μ, a.TermAs[Set[Real]]("{y:real | y ≤ t}")),
							extended_nonneg_real.ToRealNonneg.At(a.TermAs[ExtendedNonnegReal]("μ({y:real | y ≤ t})")),
							continuityFromAbove.At(
								μ,
								a.TermAs[Fun2[Nat, Real, Bool]]("λk:num. {y:real | y ≤ t + real_inv(&k + &1)}"),
								a.TermAs[Real]("extended_to_real(μ({y:real | y ≤ t}))"),
								e)),
					)
					positive := a.Have(
						"1/(k + 1) is positive",
						"&0 < real_inv(&k + &1)",
						ByArith(),
					)
					a.Show(
						"so b = t + 1/(k + 1) lies right of t",
						Witness(a.TermAs[Real]("t + real_inv(&k + &1)")),
						ByArith(near, positive),
					)
				})
		}),
})}

// DistributionFunctionLeftContinuousAtNull — at a point t of no mass the distribution function of
// a Borel probability on the line is continuous from the left: the slices
// {y ≤ t} ∖ {y ≤ t − 1/(k + 1)} shrink to the null point t, so by continuity from above one of
// them has mass below e, and the half-line at t is the half-line at t − 1/(k + 1) together with
// that slice. The slices shrinking to {t}, rather than the half-lines rising to {y < t}, take the
// left side through the same continuity from above as the right. Stated as some a < t with F(t)
// within e of F(a), it is continuity, F being increasing.
var DistributionFunctionLeftContinuousAtNull = distributionFunctionLeftContinuousAtNullThm{family.Add(registry.ProofEntry{
	Name: "DistributionFunctionLeftContinuousAtNull",
	Key:  "prop_352650e5d171771e",
	Build: family.Sections(Statement{
		Binders: "∀μ:(set(real) → extended_nonneg_real). ∀t e:real.",
		Hypotheses: []string{
			"probability_on(𝕌, borel_sets(real_topology), μ)",
			"μ({t}) = extended_of_real(&0)",
			"&0 < e",
		},
		Conclusion: "∃a:real. " +
			"    a < t ∧ extended_to_real(μ({y:real | y ≤ t})) < extended_to_real(μ({y:real | y ≤ a})) + e",
		Abbrev: Abbrev{
			{Name: "slice", Text: "λt:real. λk:num. {y:real | y ≤ t} ∖ {y:real | y ≤ t - real_inv(&k + &1)}"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			sliceMeet := ctx.Lemma("∀t y:real. (∀k:num. y ≤ t ∧ ¬(y ≤ t - real_inv(&k + &1))) ⇔ y = t",
				func(a *Argument, t, y *Expr[Real]) {
					a.Iff()
					a.Forward(
						"a point in every slice between t − 1/(k + 1) and t is t, the reciprocals falling below any gap",
						func(b *Argument, all Fact) {
							elsewhere := b.SupposeNot()
							gap := b.Have(
								"otherwise y lies left of t",
								"&0 < t - y",
								ByArith(elsewhere, all.At(b.TermAs[Nat]("0"))),
							)
							n, small := b.ObtainAs[Nat](
								"so some 1/(n + 1) lies below t − y",
								"∃n:num. real_inv(&n + &1) < t - y",
								By(gap, real_archimedean.ExistsReciprocalBelow.At(b.TermAs[Real]("t - y"))),
							)
							b.Show(
								"against y > t − 1/(n + 1)",
								ByArith(all.At(n), small),
							)
						})
					a.Backward(
						"t lies in every slice, the reciprocals being positive",
						func(b *Argument, equal Fact) {
							b.FixAs[Nat]("k")
							positive := b.Have(
								"1/(k + 1) is positive",
								"&0 < real_inv(&k + &1)",
								ByArith(),
							)
							b.Show(
								"so t ≤ t and t > t − 1/(k + 1)",
								ByArith(equal, positive),
							)
						})
				})

			return ctx.Theorem(headline,
				func(
					a *Argument,
					μ *Arrow[Set[Real], ExtendedNonnegReal],
					t, e *Expr[Real],
					probability, null, pos Fact,
				) {
					line := a.TermAs[Set[Real]]("𝕌")
					borelSets := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
					slices := a.Have(
						"the slices {y ≤ t} ∖ {y ≤ t − 1/(k + 1)}, differences of half-lines, are Borel sets",
						"∀k:num. «slice»(t, k) ∈ borel_sets(real_topology)",
						By(
							borel_function.LineBorelSigmaAlgebra,
							sigma_algebra.SigmaFiniteOperations.At(line, borelSets),
							borel_function.RaysBorel),
					)
					decreasing := a.Have(
						"they decrease, the half-lines they remove increasing",
						"∀k:num. «slice»(t, k + 1) ⊆ «slice»(t, k)",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("k")
							widening := b.Have(
								"the half-line {y ≤ t − 1/(k + 1)} lies in the next one, 1/(k + 2) ≤ 1/(k + 1)",
								"{y:real | y ≤ t - real_inv(&k + &1)} ⊆ {y:real | y ≤ t - real_inv(&(k + 1) + &1)}",
								ByArith(
									real_order_field.InvAntitoneWeak.At(b.TermAs[Real]("&k + &1"), b.TermAs[Real]("&(k + 1) + &1")),
									set_basic.SubsetDef),
							)
							b.Show(
								"so removing the larger one leaves less",
								BySets(widening),
							)
						}),
					)
					meet := a.Have(
						"the slices meet in the point t",
						"⋂image(«slice»(t), 𝕌) = {t}",
						Simp(Fwd(set_image.IntersImage)),
						BySets(At(sliceMeet, t)),
					)
					k, thin := a.ObtainAs[Nat](
						"so some slice has mass below e",
						"∃k:num. extended_to_real(μ(«slice»(t, k))) < &0 + e",
						ByArith(
							probability,
							slices,
							decreasing,
							meet,
							null,
							pos,
							continuityFromAbove.At(
								μ,
								a.TermAs[Fun2[Nat, Real, Bool]]("«slice»(t)"),
								a.TermAs[Real]("&0"),
								e)),
					)
					positive := a.Have(
						"1/(k + 1) is positive",
						"&0 < real_inv(&k + &1)",
						ByArith(),
					)
					inside := a.Have(
						"so the half-line {y ≤ t − 1/(k + 1)} lies in the one at t",
						"{y:real | y ≤ t - real_inv(&k + &1)} ⊆ {y:real | y ≤ t}",
						ByArith(positive, set_basic.SubsetDef),
					)
					leftRay := a.TermAs[Set[Real]]("{y:real | y ≤ t - real_inv(&k + &1)}")
					slice := a.TermAs[Set[Real]]("«slice»(t, k)")
					split := a.Have(
						"and the half-line at t is that half-line together with the slice",
						"μ({y:real | y ≤ t}) = μ({y:real | y ≤ t - real_inv(&k + &1)}) + μ(«slice»(t, k))",
						By(
							probability,
							inside,
							probability_space.ProbabilityOnDef.At(line, borelSets, μ),
							borel_function.RaysBorel.At(t),
							borel_function.RaysBorel.At(a.TermAs[Real]("t - real_inv(&k + &1)")),
							measure_space.MeasureAddDiff.At(
								line, borelSets, μ, leftRay, a.TermAs[Set[Real]]("{y:real | y ≤ t}"))),
					)
					realSplit := a.Have(
						"both masses finite, the real masses add the same way",
						"extended_to_real(μ({y:real | y ≤ t})) = "+
							"extended_to_real(μ({y:real | y ≤ t - real_inv(&k + &1)})) + extended_to_real(μ(«slice»(t, k)))",
						By(
							probability,
							slices.At(k),
							split,
							borel_function.RaysBorel.At(a.TermAs[Real]("t - real_inv(&k + &1)")),
							probability_space.ProbabilityEventFinite.At(line, borelSets, μ, leftRay),
							probability_space.ProbabilityEventFinite.At(line, borelSets, μ, slice),
							extended_nonneg_real.ToRealAdd.At(μ.Apply(leftRay), μ.Apply(slice))),
					)
					a.Show(
						"so a = t − 1/(k + 1) lies left of t with mass within e of the mass at t",
						Witness(a.TermAs[Real]("t - real_inv(&k + &1)")),
						ByArith(realSplit, thin, positive),
					)
				})
		}),
})}
