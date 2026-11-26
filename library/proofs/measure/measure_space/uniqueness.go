package measure_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// MeasureDeterminedByPi — two measures of the same finite total mass that
// agree on a generating π-system agree on every measurable set: the sets on
// which they agree form a λ-system, since a finite common mass cancels from
// the masses of a complement and countable additivity carries agreement
// through disjoint unions, and the λ-system contains the π-system.
var MeasureDeterminedByPi = measureDeterminedByPiThm{family.Add(registry.ProofEntry{
	Name: "MeasureDeterminedByPi",
	Key:  "prop_994bed3f54488445",
	Reading: "Equal total mass is needed because C need not " +
		"contain Ω: with C = ∅ the conclusion at Ω is μ(Ω) = ν(Ω).",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀C S:set(set(A)). ∀μ ν:(set(A) → extended_nonneg_real). ∀E:set(A).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"measure_on(Ω, S, ν)",
			"μ(Ω) = ν(Ω)",
			"μ(Ω) ≠ extended_infinity",
			"pi_system_on(Ω, C)",
			"S = generated_sigma(Ω, C)",
			"∀R:set(A). R ∈ C ⇒ μ(R) = ν(R)",
			"E ∈ S",
		},
		Conclusion: "μ(E) = ν(E)",
	}, func(
		a *Argument, Ω *Expr[Set[A]], C, S *Expr[Set[Set[A]]],
		μ, ν *Arrow[Set[A], ExtendedNonnegReal], E *Expr[Set[A]],
		μMeasure, νMeasure, total, finiteTotal, pi, generated, onGenerators, event Fact,
	) {
		sigma := a.Have(
			"the common measurable sets form a sigma algebra",
			"sigma_algebra_on(Ω, S)",
			By(μMeasure, MeasureOn.At(Ω, S, μ)))
		sigmaLaws := a.Conjuncts(
			a.Unfolded(sigma, sigma_algebra.SigmaAlgebraOnDef),
			"the measurable sets lie in the carrier",
			"the carrier is measurable",
			"relative complements are measurable",
			"countable unions are measurable")
		subsets, carrier, complement, countable := sigmaLaws[0], sigmaLaws[1], sigmaLaws[2], sigmaLaws[3]
		D, dDef := a.LetAs[Set[Set[A]]]("D", "{F:set(A) | F ∈ S ∧ μ(F) = ν(F)}")
		agreement := a.Have(
			"the agreement class contains precisely the measurable sets with equal mass",
			"∀F:set(A). F ∈ D ⇔ F ∈ S ∧ μ(F) = ν(F)",
			BySets(dDef))
		complements := a.Have(
			"agreement passes to relative complements",
			"∀F:set(A). F ∈ D ⇒ Ω ∖ F ∈ D",
			Derive(func(b *Argument) {
				F := b.FixAs[Set[A]]("F")
				member := b.Assume()
				remainder := b.TermAs[Set[A]]("Ω ∖ F")
				μrest, νrest, μF := μ.Apply(remainder), ν.Apply(remainder), μ.Apply(F)
				measurable := b.Have(
					"F and its complement are measurable and F has common mass",
					"F ∈ S ∧ Ω ∖ F ∈ S ∧ μ(F) = ν(F)",
					By(member, agreement.At(F), complement.At(F)))
				inside := b.Have(
					"F lies in the carrier",
					"F ⊆ Ω",
					BySets(measurable, subsets))
				sums := b.Have(
					"adjoining F to either complement gives the common total mass",
					"μ(Ω ∖ F) + μ(F) = μ(Ω) ∧ ν(Ω ∖ F) + μ(F) = μ(Ω)",
					By(
						μMeasure,
						νMeasure,
						measurable,
						carrier,
						inside,
						total,
						MeasureAddDiff.At(Ω, S, μ, F, Ω),
						MeasureAddDiff.At(Ω, S, ν, F, Ω),
						extended_nonneg_real.AddComm.At(μF, μrest),
						extended_nonneg_real.AddComm.At(ν.Apply(F), νrest)))
				finite := b.Have(
					"the common mass of F is finite",
					"μ(F) ≠ extended_infinity",
					By(Normalized, finiteTotal, sums, extended_nonneg_real.AddEqInfinity.At(μrest, μF)))
				equal := b.Have(
					"cancel the common finite mass to compare the complements in both directions",
					"μ(Ω ∖ F) = ν(Ω ∖ F)",
					By(
						finite,
						sums,
						extended_nonneg_real.LeRefl.At(μ.Apply(Ω)),
						extended_nonneg_real.AddLeCancel.At(μrest, νrest, μF),
						extended_nonneg_real.AddLeCancel.At(νrest, μrest, μF),
						extended_nonneg_real.LeAntisym.At(μrest, νrest)))
				b.Show(
					"the measurable complement has equal mass",
					By(measurable, equal, agreement.At(remainder)))
			}))
		disjointUnions := a.Have(
			"agreement passes to countable disjoint unions",
			"∀p:(num → set(A)). (∀n:num. p(n) ∈ D) ∧ (∀i j:num. i ≠ j ⇒ p(i) ∩ p(j) = ∅) ⇒ ⋃image(p, 𝕌) ∈ D",
			Derive(func(b *Argument) {
				events := b.FixAs[Fun[Nat, Set[A]]]("p")
				given := b.Conjuncts(
					b.Assume(),
					"each term is in the agreement class",
					"the terms are pairwise disjoint")
				members, disjoint := given[0], given[1]
				terms := b.Have(
					"the sequence consists of measurable events with identical terms in the two mass series",
					"(∀n:num. p(n) ∈ S) ∧ (λn:num. μ(p(n))) = (λn:num. ν(p(n)))",
					By(agreement, members))
				parts := b.Conjuncts(
					terms,
					"each term is measurable",
					"the two mass series have the same summands")
				measurable, sameTerms := parts[0], parts[1]
				μseries := b.Have(
					"μ adds the masses of the disjoint events",
					"μ(⋃image(p, 𝕌)) = extended_series(λn:num. μ(p(n)))",
					By(μMeasure, MeasureOn.At(Ω, S, μ), measurable, disjoint))
				νseries := b.Have(
					"ν adds the masses of the disjoint events",
					"ν(⋃image(p, 𝕌)) = extended_series(λn:num. ν(p(n)))",
					By(νMeasure, MeasureOn.At(Ω, S, ν), measurable, disjoint))
				equal := b.Have(
					"both masses are the same series",
					"μ(⋃image(p, 𝕌)) = ν(⋃image(p, 𝕌))",
					By(Normalized, b.Simplified(μseries, Fwd(sameTerms)), νseries))
				union := b.TermAs[Set[A]]("⋃image(p, 𝕌)")
				b.Show(
					"the measurable union has equal mass",
					By(agreement.At(union), countable.At(events), equal, measurable))
			}))
		inside := a.Have(
			"the agreement class consists of subsets of the carrier",
			"D ⊆ {F:set(A) | F ⊆ Ω}",
			BySets(agreement, subsets))
		whole := a.Have(
			"the whole carrier is in the agreement class",
			"Ω ∈ D",
			By(agreement.At(Ω), carrier, total))
		lambda := a.Have(
			"the agreement class is a lambda system",
			"lambda_system_on(Ω, D)",
			By(inside, whole, complements, disjointUnions, sigma_algebra.LambdaSystemDef.At(Ω, D)))
		generators := a.Have(
			"the generating pi system consists of measurable sets",
			"C ⊆ S",
			By(pi, generated, sigma_algebra.PiSystemDef.At(Ω, C), sigma_algebra.GeneratedSigmaAlgebra.At(Ω, C)))
		common := a.Have(
			"the two measures agree on the generators",
			"C ⊆ D",
			BySets(agreement, generators, onGenerators))
		a.Show(
			"pi-lambda extends the agreement to the generated sigma algebra",
			BySets(agreement.At(E), lambda, common, pi, generated, event, sigma_algebra.PiLambda.At(Ω, C, D)))
	}),
})}

// MeasureDeterminedByPiExhaustion — two measures that agree on a generating
// π-system agree on every measurable set once an increasing sequence of
// sets of the π-system, of finite mass, exhausts the carrier. Cut by K(n),
// both measures are measures on the same σ-algebra of the common finite
// total mass of K(n), and they agree on the π-system, which K(n) cuts into
// itself; so they agree on E ∩ K(n), and continuity from below along the
// increasing cuts carries the agreement to E.
var MeasureDeterminedByPiExhaustion = measureDeterminedByPiExhaustionThm{family.Add(registry.ProofEntry{
	Name: "MeasureDeterminedByPiExhaustion",
	Key:  "prop_b56d44b2e8faa145",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀C S:set(set(A)). " +
			"∀μ ν:(set(A) → extended_nonneg_real). " +
			"∀K:(num → set(A)). " +
			"∀E:set(A).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"measure_on(Ω, S, ν)",
			"pi_system_on(Ω, C)",
			"S = generated_sigma(Ω, C)",
			"∀R:set(A). R ∈ C ⇒ μ(R) = ν(R)",
			"∀n:num. K(n) ∈ C ∧ μ(K(n)) ≠ extended_infinity",
			"∀n:num. K(n) ⊆ K(n + 1)",
			"⋃image(K, 𝕌) = Ω",
			"E ∈ S",
		},
		Conclusion: "μ(E) = ν(E)",
	}, func(
		a *Argument, Ω *Expr[Set[A]], C, S *Expr[Set[Set[A]]],
		μ, ν *Arrow[Set[A], ExtendedNonnegReal], K *Arrow[Nat, Set[A]], E *Expr[Set[A]],
		μMeasure, νMeasure, pi, generated, onGenerators, finiteSets, increasing, exhaustion, event Fact,
	) {
		sigma := a.Have(
			"the common measurable sets form a sigma algebra",
			"sigma_algebra_on(Ω, S)",
			By(μMeasure, MeasureOn.At(Ω, S, μ)))
		subsets := a.Have(
			"the measurable sets lie in the carrier",
			"S ⊆ {F:set(A) | F ⊆ Ω}",
			By(sigma, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
		generators := a.Have(
			"the generating pi system consists of measurable sets",
			"C ⊆ S",
			By(pi, generated, sigma_algebra.PiSystemDef.At(Ω, C), sigma_algebra.GeneratedSigmaAlgebra.At(Ω, C)))
		members := a.Have(
			"each K(n) is a measurable subset of the carrier, of finite common mass",
			"∀n:num. K(n) ∈ S ∧ K(n) ⊆ Ω ∧ μ(K(n)) = ν(K(n)) ∧ μ(K(n)) ≠ extended_infinity",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"a generator is measurable, and the measures agree on it",
					BySets(finiteSets.At(n), generators, subsets, onGenerators.At(K.Apply(n))))
			}))
		cutEqual := a.Have(
			"the two measures agree on the cut of E by each K(n)",
			"∀n:num. μ(E ∩ K(n)) = ν(E ∩ K(n))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				Kn := K.Apply(n)
				μcut := b.TermAs[Fun[Set[A], ExtendedNonnegReal]]("restricted_measure(μ, K(n))")
				νcut := b.TermAs[Fun[Set[A], ExtendedNonnegReal]]("restricted_measure(ν, K(n))")
				restrictions := b.Have(
					"cut by K(n), both measures are measures on the carrier",
					"measure_on(Ω, S, restricted_measure(μ, K(n))) ∧ measure_on(Ω, S, restricted_measure(ν, K(n)))",
					By(
						μMeasure,
						νMeasure,
						members.At(n),
						RestrictMeasureOnCarrier.At(Ω, S, μ, Kn),
						RestrictMeasureOnCarrier.At(Ω, S, ν, Kn)))
				whole := b.Have(
					"K(n) lies in the carrier",
					"Ω ∩ K(n) = K(n)",
					BySets(members.At(n)))
				totals := b.Have(
					"the cut measures have the common finite total mass of K(n)",
					"restricted_measure(μ, K(n), Ω) = restricted_measure(ν, K(n), Ω) ∧ "+
						"restricted_measure(μ, K(n), Ω) ≠ extended_infinity",
					By(
						Normalized,
						members.At(n),
						whole,
						RestrictMeasureDef.At(μ, Kn, Ω),
						RestrictMeasureDef.At(ν, Kn, Ω)))
				onCuts := b.Have(
					"the cut measures agree on the pi system, which K(n) cuts into itself",
					"∀R:set(A). R ∈ C ⇒ restricted_measure(μ, K(n), R) = restricted_measure(ν, K(n), R)",
					Derive(func(c *Argument) {
						R := c.FixAs[Set[A]]("R")
						inC := c.Assume()
						meet := c.Have(
							"the cut of a generator is a generator",
							"R ∩ K(n) ∈ C",
							By(pi, inC, finiteSets.At(n), sigma_algebra.PiSystemDef.At(Ω, C)))
						c.Show(
							"the two measures agree on that generator",
							By(
								meet,
								onGenerators.At(c.TermAs[Set[A]]("R ∩ K(n)")),
								RestrictMeasureDef.At(μ, Kn, R),
								RestrictMeasureDef.At(ν, Kn, R)))
					}))
				b.Show(
					"two measures of equal finite mass agreeing on the pi system agree on E",
					By(
						restrictions,
						totals,
						pi,
						generated,
						onCuts,
						event,
						MeasureDeterminedByPi.At(Ω, C, S, μcut, νcut, E),
						RestrictMeasureDef.At(μ, Kn, E),
						RestrictMeasureDef.At(ν, Kn, E)))
			}))
		cuts := a.TermAs[Fun[Nat, Set[A]]]("λn:num. E ∩ K(n)")
		cutEvents := a.Have(
			"the cuts of E are measurable",
			"∀n:num. E ∩ K(n) ∈ S",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"an intersection of measurable sets",
					By(sigma, event, members.At(n), sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
			}))
		cutGrowing := a.Have(
			"the cuts of E increase with K",
			"∀n:num. E ∩ K(n) ⊆ E ∩ K(n + 1)",
			BySets(increasing))
		union := a.Have(
			"the cuts exhaust E, which lies in the carrier K exhausts",
			"⋃image(λn:num. E ∩ K(n), 𝕌) = E",
			BySets(exhaustion, event, subsets))
		μLimit := a.Have(
			"continuity from below writes μ(E) as the supremum of the masses of the cuts",
			"μ(E) = extended_sup(image(λn:num. μ(E ∩ K(n)), 𝕌))",
			By(μMeasure, cutEvents, cutGrowing, union, MeasureContinuousIncreasing.At(Ω, S, μ, cuts)))
		νLimit := a.Have(
			"and ν(E) likewise",
			"ν(E) = extended_sup(image(λn:num. ν(E ∩ K(n)), 𝕌))",
			By(νMeasure, cutEvents, cutGrowing, union, MeasureContinuousIncreasing.At(Ω, S, ν, cuts)))
		terms := a.Have(
			"the two sequences of cut masses are identical",
			"(λn:num. μ(E ∩ K(n))) = (λn:num. ν(E ∩ K(n)))",
			Funext(),
			By(cutEqual))
		a.Show(
			"the two suprema are equal",
			By(a.Simplified(μLimit, Fwd(terms)), νLimit))
	}),
})}
