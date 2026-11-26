// countable.go — the Carathéodory sets of an outer measure are closed under
// countable unions and intersections, the measure is countably additive on
// them, and so they form a σ-algebra on which the outer measure is a
// measure: Carathéodory's theorem.

package caratheodory

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/outer_measure"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// CountableUnionMeasurable — the union U of a sequence of Carathéodory
// sets is one. Make the sequence disjoint: B(n) is a(n) less the sets
// before it, a Carathéodory set as a difference of two, and a point of U
// lies in B at the least n with the point in a(n). For a test set t, the
// first B(0), …, B(n) form a Carathéodory set inside U, which cuts t into
// pieces measuring Σ_{k ≤ n} μ(t ∩ B(k)) and at least μ(t ∖ U); so the
// whole series of the μ(t ∩ B(k)) plus μ(t ∖ U) lies below μ(t), and by
// countable subadditivity the series bounds μ(t ∩ U), the union of the
// pieces t ∩ B(k).
var CountableUnionMeasurable = countableUnionMeasurableThm{family.Add(registry.ProofEntry{
	Name: "CountableUnionMeasurable",
	Key:  "prop_eb798564bc944bcc",
	Build: family.Theorem(outer_measure.OuterMeasureOn.Statement(Statement{
		Binders:    "∀a:(num → set(A)).",
		Hypotheses: []string{"∀n:num. a(n) ∈ caratheodory_sets(Ω, μ)"},
		Conclusion: "⋃image(a, 𝕌) ∈ caratheodory_sets(Ω, μ)",
		Abbrev: Abbrev{
			{Name: "U", Text: "⋃image(a, 𝕌)"},
			{Name: "before", Text: "λn:num. {y:A | ∃k:num. k < n ∧ y ∈ a(k)}"},
			{Name: "B", Text: "λn:num. a(n) ∖ «before»(n)"},
			{Name: "first", Text: "λm:num. {x:A | ∃k:num. k ≤ m ∧ x ∈ «B»(k)}"},
		},
	}), func(
		arg *Argument,
		Ω *Expr[Set[A]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		outer Fact,
		a *Arrow[Nat, Set[A]],
		measurable Fact,
	) {
		laws := arg.Conjuncts(
			arg.Unfolded(outer, outer_measure.OuterMeasureOn),
			"the empty set has measure 0",
			"inclusion increases the measure",
			"a countable union has measure at most the series of the measures")
		mono, countable := laws[1], laws[2]
		B := arg.TermAs[Fun[Nat, Set[A]]]("«B»")
		inside := arg.Have(
			"every a(n) lies in Ω",
			"∀n:num. a(n) ⊆ Ω",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"a(n) is a Carathéodory set",
					By(b.Unfolded(measurable.At(n), CaratheodorySetsDef)))
			}))
		pieces := arg.Have(
			"each B(n), a(n) less the sets before it, is a Carathéodory set",
			"∀n:num. «B»(n) ∈ caratheodory_sets(Ω, μ)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"a difference of a(n) and a finite union of Carathéodory sets",
					By(
						outer,
						measurable,
						FiniteUnionMeasurable.At(Ω, μ, a, n),
						DiffMeasurable.At(Ω, μ, a.Apply(n), b.TermAs[Set[A]]("«before»(n)"))))
			}))
		apart := arg.Have(
			"the B(n) are pairwise disjoint: the later of two avoids the earlier one's a",
			"∀j k:num. j ≠ k ⇒ disjoint(«B»(j), «B»(k))",
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				k := b.FixAs[Nat]("k")
				distinct := b.Assume()
				b.Show(
					"one of j and k is the smaller",
					BySets(distinct, nat_order.LessThanTrichotomy.At(j, k)))
			}))
		covers := arg.Have(
			"a point of some a(n) lies in B at the least such n",
			"∀x:A. (∃n:num. x ∈ a(n)) ⇒ ∃n:num. x ∈ «B»(n)",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				some := b.Assume()
				least := b.Have(
					"there is a least n with x ∈ a(n)",
					"∃n:num. x ∈ a(n) ∧ ∀m:num. m < n ⇒ x ∉ a(m)",
					By(some, nat_order.WellOrdering.At(b.TermAs[Set[Nat]]("λn:num. x ∈ a(n)"))))
				b.Show(
					"x lies in a(n) and in none before it",
					BySets(least))
			}))
		bound := arg.Have(
			"U cuts every test set into two pieces of total at most its measure",
			"∀t:set(A). t ⊆ Ω ⇒ μ(t ∩ «U») + μ(t ∖ «U») ≤ μ(t)",
			Derive(func(b *Argument) {
				t := b.FixAs[Set[A]]("t")
				tInside := b.Assume()
				outside := b.TermAs[ExtendedNonnegReal]("μ(t ∖ «U»)")
				partial := b.Have(
					"the pieces of t in B(0), …, B(n), with the part of t outside U, measure at most μ(t)",
					"∀n:num. Σ_{k∈0 .. n} μ(t ∩ «B»(k)) + μ(t ∖ «U») ≤ μ(t)",
					Derive(func(c *Argument) {
						n := c.FixAs[Nat]("n")
						first := c.Simplified(
							GroupPremises(outer, pieces, FiniteUnionMeasurable.At(Ω, μ, B, c.TermAs[Nat]("n + 1"))),
							Rev(nat_arith.Add1),
							Fwd(nat_order.LessThanSucIffLessEq))
						splits := c.Conjuncts(
							c.Unfolded(first, CaratheodorySetsDef),
							"B(0) ∪ … ∪ B(n) lies in Ω",
							"B(0) ∪ … ∪ B(n) splits every test set additively")
						beyond := c.Have(
							"what lies outside U lies outside B(0) ∪ … ∪ B(n), inside Ω",
							"t ∖ «U» ⊆ t ∖ «first»(n) ∧ t ∖ «first»(n) ⊆ Ω",
							BySets(tInside))
						c.Show(
							"B(0) ∪ … ∪ B(n) cuts t into the pieces in the B(k) and a part containing t ∖ U",
							By(
								tInside,
								splits[1].At(t),
								pieces,
								apart,
								DisjointAdditive.At(Ω, μ, B, t, n),
								beyond,
								mono.At(c.TermAs[Set[A]]("t ∖ «U»"), c.TermAs[Set[A]]("t ∖ «first»(n)")),
								extended_nonneg_real.AddLeAdd.At(
									c.TermAs[ExtendedNonnegReal]("Σ_{k∈0 .. n} μ(t ∩ «B»(k))"),
									outside,
									c.TermAs[ExtendedNonnegReal]("Σ_{k∈0 .. n} μ(t ∩ «B»(k))"),
									c.TermAs[ExtendedNonnegReal]("μ(t ∖ «first»(n))")),
								extended_nonneg_real.LeRefl))
					}))
				series := b.TermAs[ExtendedNonnegReal]("extended_series(λk:num. μ(t ∩ «B»(k)))")
				whole := b.Have(
					"so does the whole series of the pieces in the B(k)",
					"extended_series(λk:num. μ(t ∩ «B»(k))) + μ(t ∖ «U») ≤ μ(t)",
					By(partial, extended_nonneg_real.SeriesAddLe))
				covered := b.Have(
					"the pieces t ∩ B(k) lie in Ω, and their union is the part of t in U",
					"(∀k:num. t ∩ «B»(k) ⊆ Ω) ∧ ⋃image(λk:num. t ∩ «B»(k), 𝕌) = t ∩ «U»",
					BySets(tInside, covers))
				within := b.Have(
					"so countable subadditivity bounds μ(t ∩ U) by the series",
					"μ(t ∩ «U») ≤ extended_series(λk:num. μ(t ∩ «B»(k)))",
					By(covered, countable.At(b.TermAs[Fun[Nat, Set[A]]]("λk:num. t ∩ «B»(k)"))))
				b.Show(
					"hence the two pieces of t measure at most μ(t)",
					By(
						within,
						whole,
						extended_nonneg_real.AddLeMono.At(b.TermAs[ExtendedNonnegReal]("μ(t ∩ «U»)"), series, outside),
						extended_nonneg_real.LeTrans))
			}))
		union := arg.TermAs[Set[A]]("«U»")
		unionInside := arg.Have(
			"U lies in Ω",
			"«U» ⊆ Ω",
			BySets(inside))
		arg.Show(
			"so U is a Carathéodory set",
			By(outer, unionInside, bound, MeasurableIffLe.At(Ω, μ, union)))
	}),
})}

// CountableInterMeasurable — the intersection of a sequence of
// Carathéodory sets is one: inside the carrier, which holds a(0) and so
// the intersection, it is the complement of the union of their
// complements.
var CountableInterMeasurable = countableInterMeasurableThm{family.Add(registry.ProofEntry{
	Name: "CountableInterMeasurable",
	Key:  "prop_6fe0b9a660411842",
	Build: family.Theorem(outer_measure.OuterMeasureOn.Statement(Statement{
		Binders:    "∀a:(num → set(A)).",
		Hypotheses: []string{"∀n:num. a(n) ∈ caratheodory_sets(Ω, μ)"},
		Conclusion: "⋂image(a, 𝕌) ∈ caratheodory_sets(Ω, μ)",
	}), func(
		arg *Argument,
		Ω *Expr[Set[A]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		outer Fact,
		a *Arrow[Nat, Set[A]],
		measurable Fact,
	) {
		firstInside := arg.Have(
			"a(0) lies in Ω",
			"a(0) ⊆ Ω",
			By(arg.Unfolded(measurable.At(arg.TermAs[Nat]("0")), CaratheodorySetsDef)))
		deMorgan := arg.Have(
			"a point of Ω lies in every a(n) exactly when it lies in none of their complements",
			"⋂image(a, 𝕌) = Ω ∖ ⋃image(λn:num. Ω ∖ a(n), 𝕌)",
			BySets(firstInside))
		arg.Do(deMorgan.Rw())
		arg.Show(
			"so is the union of the complements, and so its complement",
			By(
				outer,
				measurable,
				ComplementMeasurable,
				At(CountableUnionMeasurable, Ω, μ, arg.TermAs[Fun[Nat, Set[A]]]("λn:num. Ω ∖ a(n)"))))
	}),
})}

// CountablyAdditive — on a pairwise disjoint sequence of Carathéodory sets
// the measure is countably additive. Countable subadditivity gives one
// inequality. For the other, the union U lies in the carrier and its
// pieces U ∩ a(k) are the a(k) themselves, so by additivity on the pieces
// each partial sum is the measure of U ∩ (a(0) ∪ … ∪ a(n)), a subset of U.
var CountablyAdditive = countablyAdditiveThm{family.Add(registry.ProofEntry{
	Name: "CountablyAdditive",
	Key:  "prop_8e5d6945b63708dd",
	Build: family.Theorem(outer_measure.OuterMeasureOn.Statement(Statement{
		Binders: "∀a:(num → set(A)).",
		Hypotheses: []string{
			"∀n:num. a(n) ∈ caratheodory_sets(Ω, μ)",
			"∀i j:num. i ≠ j ⇒ a(i) ∩ a(j) = ∅",
		},
		Conclusion: "μ(⋃image(a, 𝕌)) = extended_series(λn:num. μ(a(n)))",
		Abbrev: Abbrev{
			{Name: "U", Text: "⋃image(a, 𝕌)"},
		},
	}), func(
		arg *Argument,
		Ω *Expr[Set[A]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		outer Fact,
		a *Arrow[Nat, Set[A]],
		measurable, disjoint Fact,
	) {
		laws := arg.Conjuncts(
			arg.Unfolded(outer, outer_measure.OuterMeasureOn),
			"the empty set has measure 0",
			"inclusion increases the measure",
			"a countable union has measure at most the series of the measures")
		mono, countable := laws[1], laws[2]
		union := arg.TermAs[Set[A]]("«U»")
		inside := arg.Have(
			"every a(n) lies in Ω",
			"∀n:num. a(n) ⊆ Ω",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"a(n) is a Carathéodory set",
					By(b.Unfolded(measurable.At(n), CaratheodorySetsDef)))
			}))
		apart := arg.Have(
			"distinct terms of the sequence are disjoint",
			"∀j k:num. j ≠ k ⇒ disjoint(a(j), a(k))",
			BySets(disjoint))
		pieces := arg.Have(
			"U lies in Ω, and each a(k) lies in U",
			"«U» ⊆ Ω ∧ ∀k:num. «U» ∩ a(k) = a(k)",
			BySets(inside))
		partial := arg.Have(
			"each partial sum of the measures lies below μ(U)",
			"∀n:num. Σ_{k∈0 .. n} μ(a(k)) ≤ μ(«U»)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				first := b.TermAs[Set[A]]("{x:A | ∃k:num. k ≤ n ∧ x ∈ a(k)}")
				additive := b.Simplified(
					GroupPremises(measurable, apart, pieces, DisjointAdditive.At(Ω, μ, a, union, n)),
					Fwd(pieces))
				b.Show(
					"it is the measure of U ∩ (a(0) ∪ … ∪ a(n)), a subset of U",
					By(
						additive,
						pieces,
						set_order.InterSubset.At(union, first),
						mono.At(b.TermAs[Set[A]]("«U» ∩ {x:A | ∃k:num. k ≤ n ∧ x ∈ a(k)}"), union)))
			}))
		arg.Show(
			"subadditivity bounds μ(U) by the series, and the partial sums bound the series by μ(U)",
			By(
				partial,
				inside,
				countable.At(a),
				extended_nonneg_real.SeriesLeast,
				extended_nonneg_real.LeAntisym))
	}),
})}

// SigmaAlgebra — the Carathéodory sets of an outer measure form a σ-algebra
// on its carrier: they lie in it, hold it, and are closed under complements
// and countable unions.
var SigmaAlgebra = sigmaAlgebraThm{family.Add(registry.ProofEntry{
	Name: "SigmaAlgebra",
	Key:  "prop_c1ff8e49a859b15f",
	Build: family.Theorem(outer_measure.OuterMeasureOn.Statement(
		"sigma_algebra_on(Ω, caratheodory_sets(Ω, μ))"), func(
		a *Argument,
		Ω *Expr[Set[A]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		outer Fact,
	) {
		inside := a.Have(
			"every Carathéodory set lies in Ω",
			"caratheodory_sets(Ω, μ) ⊆ {u:set(A) | u ⊆ Ω}",
			Unfold(CaratheodorySetsDef),
			BySets())
		a.Do(Simp(Fwd(sigma_algebra.SigmaAlgebraOnDef)))
		a.Show(
			"Ω, the complements and the countable unions of Carathéodory sets are Carathéodory sets",
			By(inside, outer, CarrierMeasurable, ComplementMeasurable, CountableUnionMeasurable))
	}),
})}

// MeasureOnCaratheodory — Carathéodory's theorem: an outer measure is a
// measure on its Carathéodory sets. They form a σ-algebra, the empty set
// has measure 0, and the measure is countably additive on them.
var MeasureOnCaratheodory = measureOnCaratheodoryThm{family.Add(registry.ProofEntry{
	Name: "MeasureOnCaratheodory",
	Key:  "prop_a2984d75c0cae619",
	Build: family.Theorem(outer_measure.OuterMeasureOn.Statement(
		"measure_on(Ω, caratheodory_sets(Ω, μ), μ)"), func(
		a *Argument,
		Ω *Expr[Set[A]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		outer Fact,
	) {
		laws := a.Conjuncts(
			a.Unfolded(outer, outer_measure.OuterMeasureOn),
			"the empty set has measure 0",
			"inclusion increases the measure",
			"a countable union has measure at most the series of the measures")
		a.Do(measure_space.MeasureOn.Intro(
			Case(
				"the Carathéodory sets form a σ-algebra",
				By(outer, SigmaAlgebra)),
			Case(
				"the empty set has measure 0",
				By(laws[0])),
			Case(
				"the measure is countably additive on disjoint Carathéodory sets",
				By(outer, CountablyAdditive))))
	}),
})}
