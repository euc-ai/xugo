package measure_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// FiniteMeasureSigmaFinite — a finite measure is σ-finite: the constant
// sequence at the carrier is a cover by measurable sets of finite mass.
var FiniteMeasureSigmaFinite = finiteMeasureSigmaFiniteThm{family.Add(registry.ProofEntry{
	Name: "FiniteMeasureSigmaFinite",
	Key:  "prop_aab536c69a97953c",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real).",
		Hypotheses: []string{"finite_measure_on(Ω, S, μ)"},
		Conclusion: "sigma_finite_on(Ω, S, μ)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		finite Fact,
	) {
		laws := a.Conjuncts(
			a.Unfolded(finite, FiniteMeasureDef),
			"μ is a measure",
			"the carrier has finite mass")
		measure, finiteTotal := laws[0], laws[1]
		carrier := a.Have(
			"the carrier is measurable",
			"Ω ∈ S",
			By(measure, MeasureOn.At(Ω, S, μ), sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
		cover := a.Have(
			"the constant sequence at the carrier is a cover by measurable sets of finite mass",
			"∃a:(num → set(A)). (∀n:num. a(n) ∈ S ∧ μ(a(n)) ≠ extended_infinity) ∧ ⋃image(a, 𝕌) = Ω",
			Derive(func(b *Argument) {
				b.Take(b.TermAs[Fun[Nat, Set[A]]]("λn:num. Ω"))
				covers := b.Have(
					"the union of the constant sequence is the carrier",
					"⋃image(λn:num. Ω, 𝕌) = Ω",
					BySets())
				b.Show(
					"every term is the carrier",
					By(carrier, finiteTotal, covers))
			}))
		a.Show(
			"a measure with such a cover is σ-finite",
			By(measure, cover, SigmaFiniteDef.At(Ω, S, μ)))
	}),
})}

// SigmaFiniteIncreasingCover — the carrier of a σ-finite measure is the
// union of an increasing sequence of measurable sets of finite mass: the
// unions of the sets of a finite-mass cover taken before each index. Each
// such union adjoins one set of finite mass to the one before it, so its
// mass stays finite.
var SigmaFiniteIncreasingCover = sigmaFiniteIncreasingCoverThm{family.Add(registry.ProofEntry{
	Name: "SigmaFiniteIncreasingCover",
	Key:  "prop_cd9505d5be4ebd36",
	Build: family.Sections(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real).",
		Hypotheses: []string{"sigma_finite_on(Ω, S, μ)"},
		Conclusion: "∃a:(num → set(A)). " +
			"    (∀n:num. a(n) ∈ S ∧ μ(a(n)) ≠ extended_infinity) ∧ " +
			"    (∀n:num. a(n) ⊆ a(n + 1)) ∧ " +
			"    ⋃image(a, 𝕌) = Ω",
		Abbrev: Abbrev{
			{Name: "earlier", Text: "λa:(num → set(A)). λn:num. ⋃image(a, {k:num | k < n})"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		finiteUnion := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀F G:set(A).",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"F ∈ S",
				"G ∈ S",
				"μ(F) ≠ extended_infinity",
				"μ(G) ≠ extended_infinity",
			},
			Conclusion: "F ∪ G ∈ S ∧ μ(F ∪ G) ≠ extended_infinity",
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
			F, G *Expr[Set[A]], measure, inF, inG, finiteF, finiteG Fact) {
			newPart := a.TermAs[Set[A]]("G ∖ F")
			events := a.Have(
				"the union and the part of G outside F are both measurable",
				"F ∪ G ∈ S ∧ G ∖ F ∈ S",
				By(measure, inF, inG, MeasureOn.At(Ω, S, μ), sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
			subset := a.Have(
				"the new part is contained in G",
				"G ∖ F ⊆ G",
				BySets())
			finitePart := a.Have(
				"the new part has finite mass by monotonicity",
				"μ(G ∖ F) ≠ extended_infinity",
				By(
					measure,
					inG,
					events,
					subset,
					finiteG,
					MeasureMono.At(Ω, S, μ, newPart, G),
					extended_nonneg_real.ExtendedLeDef.At(μ.Apply(newPart), μ.Apply(G))))
			partition := a.Have(
				"F and the new part partition the union",
				"F ∪ (G ∖ F) = F ∪ G ∧ F ∩ (G ∖ F) = ∅",
				BySets())
			a.Show(
				"the union adds two finite masses",
				By(
					Normalized,
					measure,
					inF,
					events,
					partition,
					finiteF,
					finitePart,
					MeasureAdditive.At(Ω, S, μ, F, newPart),
					extended_nonneg_real.AddEqInfinity.At(μ.Apply(F), μ.Apply(newPart))))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			sigmaFinite Fact,
		) {
			finiteness := a.Conjuncts(
				a.Unfolded(sigmaFinite, SigmaFiniteDef),
				"μ is a measure",
				"the carrier admits a countable finite-mass cover")
			measure := finiteness[0]
			_, cover := a.UnpackAs[Fun[Nat, Set[A]]](finiteness[1], "q")
			covered := a.Conjuncts(
				cover,
				"the cover has measurable sets of finite mass",
				"the cover fills Ω")
			sets, fills := covered[0], covered[1]
			base := a.Have(
				"the measurable sets form a σ-algebra and the empty set has zero mass",
				"sigma_algebra_on(Ω, S) ∧ μ(∅) = &0",
				By(measure, MeasureOn.At(Ω, S, μ)))
			earlierUnions := a.Have(
				"every union of earlier cover sets is measurable and has finite mass",
				"∀n:num. «earlier»(q, n) ∈ S ∧ μ(«earlier»(q, n)) ≠ extended_infinity",
				Derive(func(b *Argument) {
					b.Induct("n")
					b.Base(
						"before index zero the union is empty, with zero mass",
						func(c *Argument) {
							empty := c.Have(
								"there are no indices before zero",
								"«earlier»(q, 0) = ∅",
								BySets(nat_order.LessThanZeroClause))
							c.Show(
								"the empty set is measurable and has finite mass",
								By(empty, base, sigma_algebra.SigmaFiniteOperations.At(Ω, S), extended_nonneg_real.ZeroNotInfinity))
						})
					b.Step(
						"adjoining the next cover set preserves finite mass",
						func(c *Argument, previous Fact) {
							n := c.TermAs[Nat]("n")
							earlier := c.TermAs[Set[A]]("«earlier»(q, n)")
							next := c.TermAs[Set[A]]("q(n)")
							grown := c.Have(
								"the union of the sets before suc(n) adds the term at n",
								"«earlier»(q, suc(n)) = «earlier»(q, n) ∪ q(n)",
								BySets(nat_order.LessThanSucClause))
							c.Show(
								"the union combines two measurable sets of finite mass",
								By(measure, previous, sets.At(n), grown, At(finiteUnion, Ω, S, μ, earlier, next)))
						})
				}))
			increasing := a.Have(
				"the earlier unions are increasing",
				"∀n:num. «earlier»(q, n) ⊆ «earlier»(q, n + 1)",
				Derive(func(b *Argument) {
					indices := b.Have(
						"an index below n is also below n + 1",
						"∀n k:num. k < n ⇒ k < n + 1",
						ByArith())
					b.Show(
						"the larger index set collects all the earlier sets",
						BySets(indices))
				}))
			exhausts := a.Have(
				"the increasing earlier unions exhaust the carrier",
				"⋃image(λn:num. «earlier»(q, n), 𝕌) = Ω",
				Derive(func(b *Argument) {
					indices := b.Have(
						"each index lies below its successor",
						"∀n:num. n < n + 1",
						ByArith())
					b.Show(
						"each cover set lies in the earlier union one index on",
						BySets(fills, indices))
				}))
			a.Do(Witness(a.TermAs[Fun[Nat, Set[A]]]("λn:num. «earlier»(q, n)")))
			a.Show(
				"the earlier unions are an increasing cover by sets of finite mass",
				By(earlierUnions, increasing, exhausts))
		})
	}),
})}
