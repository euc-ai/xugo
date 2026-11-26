// closure.go — the first closure properties of the Carathéodory sets of an
// outer measure: the one-inequality criterion, complements, the empty set,
// the carrier and the null sets.

package caratheodory

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/outer_measure"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// MeasurableIffLe — Carathéodory's criterion needs one inequality only: a
// subset s of the carrier is a Carathéodory set as soon as it cuts every
// test set t into two pieces of total measure at most μ(t). The other
// inequality is subadditivity, t being the union of its two pieces.
var MeasurableIffLe = measurableIffLeThm{family.Add(registry.ProofEntry{
	Name: "MeasurableIffLe",
	Key:  "prop_4c306c50ac77f470",
	Build: family.Theorem(outer_measure.OuterMeasureOn.Statement(Statement{
		Binders:    "∀s:set(A).",
		Hypotheses: []string{"s ⊆ Ω"},
		Conclusion: "s ∈ caratheodory_sets(Ω, μ) ⇔ ∀t:set(A). t ⊆ Ω ⇒ μ(t ∩ s) + μ(t ∖ s) ≤ μ(t)",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		outer Fact,
		s *Expr[Set[A]],
		inside Fact,
	) {
		a.Do(Unfold(CaratheodorySetsDef))
		a.Iff()
		a.Forward(
			"an equation is in particular an inequality",
			func(b *Argument, measurable Fact) {
				parts := b.Conjuncts(
					measurable,
					"s lies in Ω",
					"s splits every test set additively")
				t := b.FixAs[Set[A]]("t")
				tInside := b.Assume()
				b.Show(
					"the two pieces add up to μ(t)",
					By(tInside, parts[1].At(t), extended_nonneg_real.LeRefl))
			})
		a.Backward(
			"subadditivity gives the other inequality",
			func(b *Argument, below Fact) {
				splits := b.Have(
					"s splits every test set additively",
					"∀t:set(A). t ⊆ Ω ⇒ μ(t) = μ(t ∩ s) + μ(t ∖ s)",
					Derive(func(c *Argument) {
						t := c.FixAs[Set[A]]("t")
						tInside := c.Assume()
						pieces := c.Have(
							"the two pieces of t lie in Ω",
							"t ∩ s ⊆ Ω ∧ t ∖ s ⊆ Ω",
							BySets(tInside))
						cover := c.Have(
							"t is the union of its two pieces",
							"(t ∩ s) ∪ (t ∖ s) = t",
							BySets())
						c.Show(
							"so μ(t) lies below the sum of the two, and the two inequalities meet",
							By(
								tInside,
								below.At(t),
								outer,
								pieces,
								cover,
								outer_measure.Subadditive.At(
									Ω, μ, c.TermAs[Set[A]]("t ∩ s"), c.TermAs[Set[A]]("t ∖ s")),
								extended_nonneg_real.LeAntisym))
					}))
				b.Show(
					"s lies in Ω and splits every test set additively",
					By(inside, splits))
			})
	}),
})}

// ComplementMeasurable — the complement in the carrier of a Carathéodory
// set is a Carathéodory set: inside the carrier, cutting t by Ω ∖ s gives
// the same two pieces as cutting it by s, in the other order. No property
// of μ enters.
var ComplementMeasurable = complementMeasurableThm{family.Add(registry.ProofEntry{
	Name: "ComplementMeasurable",
	Key:  "prop_d57f0aa729076641",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀μ:(set(A) → extended_nonneg_real). ∀s:set(A).",
		Hypotheses: []string{"s ∈ caratheodory_sets(Ω, μ)"},
		Conclusion: "Ω ∖ s ∈ caratheodory_sets(Ω, μ)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		s *Expr[Set[A]],
		measurable Fact,
	) {
		parts := a.Conjuncts(
			a.Unfolded(measurable, CaratheodorySetsDef),
			"s lies in Ω",
			"s splits every test set additively")
		splits := a.Have(
			"so does its complement",
			"∀t:set(A). t ⊆ Ω ⇒ μ(t) = μ(t ∩ (Ω ∖ s)) + μ(t ∖ (Ω ∖ s))",
			Derive(func(b *Argument) {
				t := b.FixAs[Set[A]]("t")
				tInside := b.Assume()
				swapped := b.Have(
					"inside Ω the complement of s cuts t into the same two pieces, swapped",
					"t ∩ (Ω ∖ s) = t ∖ s ∧ t ∖ (Ω ∖ s) = t ∩ s",
					BySets(tInside))
				b.Show(
					"so the split of t by Ω ∖ s is its split by s, the terms commuted",
					By(tInside, parts[1].At(t), swapped, extended_nonneg_real.AddComm))
			}))
		a.Do(Unfold(CaratheodorySetsDef))
		a.Show(
			"Ω ∖ s lies in Ω and splits every test set additively",
			By(set_order.SubsetDiff.At(Ω, s), splits))
	}),
})}

// EmptyMeasurable — the empty set is a Carathéodory set: it cuts t into ∅,
// of measure 0, and t itself.
var EmptyMeasurable = emptyMeasurableThm{family.Add(registry.ProofEntry{
	Name: "EmptyMeasurable",
	Key:  "prop_5235ad2fbbf09ab",
	Build: family.Theorem(outer_measure.OuterMeasureOn.Statement("∅ ∈ caratheodory_sets(Ω, μ)"), func(
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
		splits := a.Have(
			"∅ splits every test set additively",
			"∀t:set(A). t ⊆ Ω ⇒ μ(t) = μ(t ∩ ∅) + μ(t ∖ ∅)",
			Derive(func(b *Argument) {
				t := b.FixAs[Set[A]]("t")
				b.Show(
					"t ∩ ∅ is ∅, of measure 0, and t ∖ ∅ is t",
					By(
						Normalized,
						set_algebra.InterEmpty.At(t),
						set_algebra.DiffEmpty.At(t),
						laws[0],
						extended_nonneg_real.AddComm,
						extended_nonneg_real.AddZero))
			}))
		a.Do(Unfold(CaratheodorySetsDef))
		a.Show(
			"∅ lies in Ω and splits every test set additively",
			By(set_order.EmptySubset.At(Ω), splits))
	}),
})}

// CarrierMeasurable — the carrier is a Carathéodory set: it cuts a test
// set t inside it into t itself and ∅, of measure 0.
var CarrierMeasurable = carrierMeasurableThm{family.Add(registry.ProofEntry{
	Name: "CarrierMeasurable",
	Key:  "prop_aa6d112b8dfa5c71",
	Build: family.Theorem(outer_measure.OuterMeasureOn.Statement("Ω ∈ caratheodory_sets(Ω, μ)"), func(
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
		splits := a.Have(
			"Ω splits every test set additively",
			"∀t:set(A). t ⊆ Ω ⇒ μ(t) = μ(t ∩ Ω) + μ(t ∖ Ω)",
			Derive(func(b *Argument) {
				b.FixAs[Set[A]]("t")
				tInside := b.Assume()
				pieces := b.Have(
					"t ∩ Ω is t, and t ∖ Ω is ∅",
					"t ∩ Ω = t ∧ t ∖ Ω = ∅",
					BySets(tInside))
				b.Show(
					"and ∅ has measure 0",
					By(pieces, laws[0], extended_nonneg_real.AddZero))
			}))
		a.Do(Unfold(CaratheodorySetsDef))
		a.Show(
			"Ω lies in itself and splits every test set additively",
			By(set_order.SubsetRefl.At(Ω), splits))
	}),
})}

// NullMeasurable — the Carathéodory sets are complete: a subset of the
// carrier of measure 0 is a Carathéodory set. Its piece of any test set t
// lies in it and is null, and the other piece lies in t, so the criterion's
// one inequality holds.
var NullMeasurable = nullMeasurableThm{family.Add(registry.ProofEntry{
	Name: "NullMeasurable",
	Key:  "prop_96d36e4da613842a",
	Build: family.Theorem(outer_measure.OuterMeasureOn.Statement(Statement{
		Binders:    "∀s:set(A).",
		Hypotheses: []string{"s ⊆ Ω", "μ(s) = &0"},
		Conclusion: "s ∈ caratheodory_sets(Ω, μ)",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		outer Fact,
		s *Expr[Set[A]],
		inside, null Fact,
	) {
		laws := a.Conjuncts(
			a.Unfolded(outer, outer_measure.OuterMeasureOn),
			"the empty set has measure 0",
			"inclusion increases the measure",
			"a countable union has measure at most the series of the measures")
		mono := laws[1]
		bound := a.Have(
			"s cuts every test set into two pieces of total at most its measure",
			"∀t:set(A). t ⊆ Ω ⇒ μ(t ∩ s) + μ(t ∖ s) ≤ μ(t)",
			Derive(func(b *Argument) {
				t := b.FixAs[Set[A]]("t")
				tInside := b.Assume()
				piece := b.TermAs[Set[A]]("t ∩ s")
				zero := b.Have(
					"t ∩ s lies in the null set s, so it is null",
					"μ(t ∩ s) = &0",
					By(
						null,
						inside,
						set_order.InterSubset.At(s, t),
						mono.At(piece, s),
						extended_nonneg_real.ZeroLe,
						extended_nonneg_real.LeAntisym))
				b.Show(
					"and t ∖ s lies in t",
					By(
						zero,
						tInside,
						set_order.SubsetDiff.At(t, s),
						mono.At(b.TermAs[Set[A]]("t ∖ s"), t),
						extended_nonneg_real.AddComm,
						extended_nonneg_real.AddZero))
			}))
		a.Show(
			"so s is a Carathéodory set",
			By(outer, inside, bound, At(MeasurableIffLe, Ω, μ, s)))
	}),
})}
