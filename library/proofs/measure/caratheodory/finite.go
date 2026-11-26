// finite.go — the Carathéodory sets of an outer measure are closed under
// finite unions, intersections and differences, and the measure adds up
// over the pieces finitely many disjoint ones cut from any test set.

package caratheodory

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/outer_measure"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// UnionMeasurable — the union of two Carathéodory sets is one. Split t by
// s, then t ∖ s by u: the piece of t in s ∪ u is t ∩ s together with
// (t ∖ s) ∩ u, and the piece outside it is (t ∖ s) ∖ u; by subadditivity
// the three measures add up to at most μ(t).
var UnionMeasurable = unionMeasurableThm{family.Add(registry.ProofEntry{
	Name: "UnionMeasurable",
	Key:  "prop_42307de583b581ec",
	Build: family.Theorem(outer_measure.OuterMeasureOn.Statement(Statement{
		Binders: "∀s u:set(A).",
		Hypotheses: []string{
			"s ∈ caratheodory_sets(Ω, μ)",
			"u ∈ caratheodory_sets(Ω, μ)",
		},
		Conclusion: "s ∪ u ∈ caratheodory_sets(Ω, μ)",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		outer Fact,
		s, u *Expr[Set[A]],
		sMeasurable, uMeasurable Fact,
	) {
		sParts := a.Conjuncts(
			a.Unfolded(sMeasurable, CaratheodorySetsDef),
			"s lies in Ω",
			"s splits every test set additively")
		uParts := a.Conjuncts(
			a.Unfolded(uMeasurable, CaratheodorySetsDef),
			"u lies in Ω",
			"u splits every test set additively")
		bound := a.Have(
			"s ∪ u cuts every test set into two pieces of total at most its measure",
			"∀t:set(A). t ⊆ Ω ⇒ μ(t ∩ (s ∪ u)) + μ(t ∖ (s ∪ u)) ≤ μ(t)",
			Derive(func(b *Argument) {
				t := b.FixAs[Set[A]]("t")
				tInside := b.Assume()
				cut := b.Have(
					"t ∩ (s ∪ u) is t ∩ s together with (t ∖ s) ∩ u, and t ∖ (s ∪ u) is (t ∖ s) ∖ u",
					"t ∩ (s ∪ u) = t ∩ s ∪ (t ∖ s) ∩ u ∧ t ∖ (s ∪ u) = (t ∖ s) ∖ u",
					BySets())
				inside := b.Have(
					"t ∩ s, (t ∖ s) ∩ u and t ∖ s lie in Ω",
					"t ∩ s ⊆ Ω ∧ (t ∖ s) ∩ u ⊆ Ω ∧ t ∖ s ⊆ Ω",
					BySets(tInside))
				pieces := b.Have(
					"so the two pieces of t measure at most μ(t ∩ s) + μ((t ∖ s) ∩ u) and μ((t ∖ s) ∖ u)",
					"μ(t ∩ (s ∪ u)) ≤ μ(t ∩ s) + μ((t ∖ s) ∩ u) ∧ μ(t ∖ (s ∪ u)) ≤ μ((t ∖ s) ∖ u)",
					By(
						cut,
						outer,
						inside,
						outer_measure.Subadditive.At(Ω, μ, b.TermAs[Set[A]]("t ∩ s"), b.TermAs[Set[A]]("(t ∖ s) ∩ u")),
						extended_nonneg_real.LeRefl))
				b.Show(
					"u splits t ∖ s and s splits t, so the three measures add up to μ(t)",
					By(
						pieces,
						tInside,
						inside,
						sParts[1].At(t),
						uParts[1].At(b.TermAs[Set[A]]("t ∖ s")),
						extended_nonneg_real.AddLeAdd.At(
							b.TermAs[ExtendedNonnegReal]("μ(t ∩ (s ∪ u))"),
							b.TermAs[ExtendedNonnegReal]("μ(t ∖ (s ∪ u))"),
							b.TermAs[ExtendedNonnegReal]("μ(t ∩ s) + μ((t ∖ s) ∩ u)"),
							b.TermAs[ExtendedNonnegReal]("μ((t ∖ s) ∖ u)")),
						extended_nonneg_real.AddAssoc.At(
							b.TermAs[ExtendedNonnegReal]("μ(t ∩ s)"),
							b.TermAs[ExtendedNonnegReal]("μ((t ∖ s) ∩ u)"),
							b.TermAs[ExtendedNonnegReal]("μ((t ∖ s) ∖ u)"))))
			}))
		inside := a.Have(
			"s ∪ u lies in Ω",
			"s ∪ u ⊆ Ω",
			BySets(sParts[0], uParts[0]))
		a.Show(
			"so s ∪ u is a Carathéodory set",
			By(outer, inside, bound, MeasurableIffLe.At(Ω, μ, a.TermAs[Set[A]]("s ∪ u"))))
	}),
})}

// InterMeasurable — the intersection of two Carathéodory sets is one,
// being, inside the carrier, the complement of the union of their
// complements.
var InterMeasurable = interMeasurableThm{family.Add(registry.ProofEntry{
	Name: "InterMeasurable",
	Key:  "prop_654ca5fc9104c5b7",
	Build: family.Theorem(outer_measure.OuterMeasureOn.Statement(Statement{
		Binders: "∀s u:set(A).",
		Hypotheses: []string{
			"s ∈ caratheodory_sets(Ω, μ)",
			"u ∈ caratheodory_sets(Ω, μ)",
		},
		Conclusion: "s ∩ u ∈ caratheodory_sets(Ω, μ)",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		outer Fact,
		s, u *Expr[Set[A]],
		sMeasurable, uMeasurable Fact,
	) {
		sParts := a.Conjuncts(
			a.Unfolded(sMeasurable, CaratheodorySetsDef),
			"s lies in Ω",
			"s splits every test set additively")
		deMorgan := a.Have(
			"inside Ω, s ∩ u is the complement of (Ω ∖ s) ∪ (Ω ∖ u)",
			"s ∩ u = Ω ∖ ((Ω ∖ s) ∪ (Ω ∖ u))",
			BySets(sParts[0]))
		a.Do(deMorgan.Rw())
		a.Show(
			"complements and the union of Carathéodory sets are Carathéodory sets",
			By(
				sMeasurable,
				uMeasurable,
				outer,
				ComplementMeasurable.At(Ω, μ, s),
				ComplementMeasurable.At(Ω, μ, u),
				At(UnionMeasurable, Ω, μ, a.TermAs[Set[A]]("Ω ∖ s"), a.TermAs[Set[A]]("Ω ∖ u")),
				ComplementMeasurable.At(Ω, μ, a.TermAs[Set[A]]("(Ω ∖ s) ∪ (Ω ∖ u)"))))
	}),
})}

// DiffMeasurable — the difference of two Carathéodory sets is one, being,
// inside the carrier, the intersection of the first with the complement of
// the second.
var DiffMeasurable = diffMeasurableThm{family.Add(registry.ProofEntry{
	Name: "DiffMeasurable",
	Key:  "prop_ee526c4e4b0215de",
	Build: family.Theorem(outer_measure.OuterMeasureOn.Statement(Statement{
		Binders: "∀s u:set(A).",
		Hypotheses: []string{
			"s ∈ caratheodory_sets(Ω, μ)",
			"u ∈ caratheodory_sets(Ω, μ)",
		},
		Conclusion: "s ∖ u ∈ caratheodory_sets(Ω, μ)",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		outer Fact,
		s, u *Expr[Set[A]],
		sMeasurable, uMeasurable Fact,
	) {
		sParts := a.Conjuncts(
			a.Unfolded(sMeasurable, CaratheodorySetsDef),
			"s lies in Ω",
			"s splits every test set additively")
		cut := a.Have(
			"inside Ω, s ∖ u is s ∩ (Ω ∖ u)",
			"s ∖ u = s ∩ (Ω ∖ u)",
			BySets(sParts[0]))
		a.Do(cut.Rw())
		a.Show(
			"the complement of u is a Carathéodory set, and so is its intersection with s",
			By(
				sMeasurable,
				uMeasurable,
				outer,
				ComplementMeasurable.At(Ω, μ, u),
				At(InterMeasurable, Ω, μ, s, a.TermAs[Set[A]]("Ω ∖ u"))))
	}),
})}

// FiniteUnionMeasurable — the union of the first n sets of a sequence of
// Carathéodory sets is one. By induction on n: below 0 there is no index,
// and the union below n + 1 is the union below n together with E(n).
var FiniteUnionMeasurable = finiteUnionMeasurableThm{family.Add(registry.ProofEntry{
	Name: "FiniteUnionMeasurable",
	Key:  "prop_18bc434997c3aeea",
	Build: family.Theorem(outer_measure.OuterMeasureOn.Statement(Statement{
		Binders:    "∀E:(num → set(A)). ∀n:num.",
		Hypotheses: []string{"∀k:num. E(k) ∈ caratheodory_sets(Ω, μ)"},
		Conclusion: "{x:A | ∃k:num. k < n ∧ x ∈ E(k)} ∈ caratheodory_sets(Ω, μ)",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		outer Fact,
		E *Arrow[Nat, Set[A]],
		measurable Fact,
	) {
		a.Induct("n")
		a.Base(
			"no index lies below 0, so the union is empty",
			func(b *Argument) {
				none := b.Have(
					"the union of no sets is empty",
					"{x:A | ∃k:num. k < 0 ∧ x ∈ E(k)} = ∅",
					BySets(nat_order.LessThanZeroClause))
				b.Show(
					"and ∅ is a Carathéodory set",
					none.Rw(),
					By(outer, EmptyMeasurable))
			})
		a.Step(
			"the indices below n + 1 are those below n and n itself",
			func(b *Argument, ih Fact) {
				b.Do(Simp(Fwd(nat_arith.Add1)))
				n := b.TermAs[Nat]("n")
				segment := b.Have(
					"the union below n + 1 is the union below n together with E(n)",
					"{x:A | ∃k:num. k < n + 1 ∧ x ∈ E(k)} = {x:A | ∃k:num. k < n ∧ x ∈ E(k)} ∪ E(n)",
					BySets(nat_order.LessThanSucClause, nat_arith.Add1))
				b.Do(segment.Rw())
				b.Show(
					"a union of two Carathéodory sets",
					By(
						ih,
						measurable.At(n),
						outer,
						At(UnionMeasurable, Ω, μ, b.TermAs[Set[A]]("{x:A | ∃k:num. k < n ∧ x ∈ E(k)}"), E.Apply(n))))
			})
	}),
})}

// DisjointAdditive — the measure adds up over the pieces a disjoint
// sequence of Carathéodory sets cuts from a test set t: t ∩ (E(0) ∪ … ∪
// E(n)) measures Σ_{k ≤ n} μ(t ∩ E(k)). By induction on n. The union up to
// n + 1 is the union up to n together with E(n + 1), which meets none of
// the earlier sets; so E(n + 1), being a Carathéodory set, cuts
// t ∩ (E(0) ∪ … ∪ E(n + 1)), a test set inside the carrier, into
// t ∩ E(n + 1) and t ∩ (E(0) ∪ … ∪ E(n)), and the second measures the sum
// up to n. No property of μ enters.
var DisjointAdditive = disjointAdditiveThm{family.Add(registry.ProofEntry{
	Name: "DisjointAdditive",
	Key:  "prop_1209b505c0b5b9ab",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀μ:(set(A) → extended_nonneg_real). ∀E:(num → set(A)). ∀t:set(A). ∀n:num.",
		Hypotheses: []string{
			"∀k:num. E(k) ∈ caratheodory_sets(Ω, μ)",
			"∀j k:num. j ≠ k ⇒ disjoint(E(j), E(k))",
			"t ⊆ Ω",
		},
		Conclusion: "μ(t ∩ {x:A | ∃k:num. k ≤ n ∧ x ∈ E(k)}) = Σ_{k∈0 .. n} μ(t ∩ E(k))",
		Abbrev: Abbrev{
			{Name: "union", Text: "λm:num. {x:A | ∃k:num. k ≤ m ∧ x ∈ E(k)}"},
		},
	}, func(
		arg *Argument,
		Ω *Expr[Set[A]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		E *Arrow[Nat, Set[A]],
		t *Expr[Set[A]],
		measurable, disjoint, inside Fact,
	) {
		arg.Induct("n")
		arg.Base(
			"up to 0 the union is E(0) alone, and so is the sum",
			func(b *Argument) {
				first := b.Have(
					"the only index up to 0 is 0",
					"«union»(0) = E(0)",
					BySets(nat_order.LessEqZeroClause))
				b.Show(
					"so both sides are μ(t ∩ E(0))",
					By(first, extended_nonneg_real.SumSegmentZero))
			})
		arg.Step(
			"E(n + 1) splits off its own piece of t",
			func(b *Argument, ih Fact) {
				b.Do(Simp(Fwd(nat_arith.Add1)))
				segment := b.Have(
					"the union up to n + 1 is the union up to n together with E(n + 1)",
					"«union»(n + 1) = «union»(n) ∪ E(n + 1)",
					BySets(nat_order.LessEqSucClause, nat_arith.Add1))
				earlier := b.Have(
					"E(n + 1) meets none of the sets before it",
					"∀k:num. k ≤ n ⇒ disjoint(E(k), E(n + 1))",
					ByArith(disjoint))
				pieces := b.Have(
					"so E(n + 1) cuts t ∩ (E(0) ∪ … ∪ E(n + 1)) into t ∩ E(n + 1) and t ∩ (E(0) ∪ … ∪ E(n))",
					"t ∩ («union»(n) ∪ E(n + 1)) ∩ E(n + 1) = t ∩ E(n + 1) ∧ "+
						"t ∩ («union»(n) ∪ E(n + 1)) ∖ E(n + 1) = t ∩ «union»(n)",
					BySets(earlier))
				test := b.TermAs[Set[A]]("t ∩ («union»(n) ∪ E(n + 1))")
				testInside := b.Have(
					"that piece of t lies in Ω",
					"t ∩ («union»(n) ∪ E(n + 1)) ⊆ Ω",
					BySets(inside))
				splits := b.Conjuncts(
					b.Unfolded(measurable.At(b.TermAs[Nat]("n + 1")), CaratheodorySetsDef),
					"E(n + 1) lies in Ω",
					"E(n + 1) splits every test set additively")
				b.Do(segment.Rw())
				b.Show(
					"the piece in E(n + 1) is the new term of the sum, the rest the sum up to n",
					By(
						testInside,
						splits[1].At(test),
						pieces,
						ih,
						extended_nonneg_real.SumSegmentPeel.At(
							b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λk:num. μ(t ∩ E(k))"),
							b.TermAs[Nat]("n")),
						extended_nonneg_real.AddComm))
			})
	}),
})}

// FiniteAdditive — the measure adds up over the pieces finitely many
// disjoint Carathéodory sets cut from a test set t. By induction over the
// finite index set: a new index a brings the set E(a), which meets none of
// the earlier ones; being a Carathéodory set, it cuts t ∩ ⋃_{insert(a, u)} E,
// a test set inside the carrier, into t ∩ E(a) and t ∩ ⋃_u E, and the
// second measures the sum over u.
var FiniteAdditive = finiteAdditiveThm{family.Add(registry.ProofEntry{
	Name: "FiniteAdditive",
	Key:  "prop_cdacee6a54fca082",
	Build: family.Theorem(outer_measure.OuterMeasureOn.Statement(Statement{
		Binders: "∀E:(B → set(A)). ∀k:set(B). ∀t:set(A).",
		Hypotheses: []string{
			"finite(k)",
			"∀i:B. i ∈ k ⇒ E(i) ∈ caratheodory_sets(Ω, μ)",
			"∀i j:B. i ∈ k ∧ j ∈ k ∧ i ≠ j ⇒ disjoint(E(i), E(j))",
			"t ⊆ Ω",
		},
		Conclusion: "μ(t ∩ {x:A | ∃i:B. i ∈ k ∧ x ∈ E(i)}) = Σ_{i∈k} μ(t ∩ E(i))",
	}), func(
		arg *Argument,
		Ω *Expr[Set[A]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		outer Fact,
		E *Arrow[B, Set[A]],
		k *Expr[Set[B]],
		t *Expr[Set[A]],
		finite, measurable, disjoint, inside Fact,
	) {
		laws := arg.Conjuncts(
			arg.Unfolded(outer, outer_measure.OuterMeasureOn),
			"the empty set has measure 0",
			"inclusion increases the measure",
			"a countable union has measure at most the series of the measures")
		arg.Show(
			"the measure is additive over every finite index set of disjoint Carathéodory sets, and k is one",
			ByInduction(finite_set.FiniteInductFresh, finite, Generalizing(measurable, disjoint), Case(
				"over ∅ the union is empty and the sum is 0",
				Derive(func(b *Argument) {
					empty := b.Have(
						"no index, no point of the union",
						"t ∩ {x:A | ∃i:B. i ∈ ∅ ∧ x ∈ E(i)} = ∅",
						BySets())
					b.Show(
						"so both sides are 0",
						By(empty, laws[0], extended_nonneg_real.SumClauses))
				})),
				Case(
					"a new index a brings a set E(a) that cuts its own piece off t",
					Derive(func(b *Argument) {
						b.FixAs[B]("a")
						b.FixAs[Set[B]]("u")
						previous := b.Assume()
						onInsert := b.Assume()
						restricted := b.Have(
							"the hypotheses hold on u, which lies inside insert(a, u)",
							"(∀i:B. i ∈ u ⇒ E(i) ∈ caratheodory_sets(Ω, μ)) ∧ "+
								"(∀i j:B. i ∈ u ∧ j ∈ u ∧ i ≠ j ⇒ disjoint(E(i), E(j)))",
							BySets(onInsert))
						earlier := b.Have(
							"so the union over u measures the sum over u",
							"μ(t ∩ {x:A | ∃i:B. i ∈ u ∧ x ∈ E(i)}) = Σ_{i∈u} μ(t ∩ E(i))",
							By(restricted, previous))
						apart := b.Have(
							"a is new, so E(a) meets none of the sets indexed by u",
							"∀i:B. i ∈ u ⇒ disjoint(E(i), E(a))",
							BySets(onInsert, previous))
						pieces := b.Have(
							"E(a) cuts the union over insert(a, u) into t ∩ E(a) and the union over u",
							"(t ∩ {x:A | ∃i:B. i ∈ insert(a, u) ∧ x ∈ E(i)}) ∩ E(a) = t ∩ E(a) ∧ "+
								"(t ∩ {x:A | ∃i:B. i ∈ insert(a, u) ∧ x ∈ E(i)}) ∖ E(a) = t ∩ {x:A | ∃i:B. i ∈ u ∧ x ∈ E(i)}",
							BySets(apart))
						newMeasurable := b.Have(
							"E(a) is a Carathéodory set",
							"E(a) ∈ caratheodory_sets(Ω, μ)",
							By(onInsert, set_basic.InInsert))
						splits := b.Conjuncts(
							b.Unfolded(newMeasurable, CaratheodorySetsDef),
							"E(a) lies in Ω",
							"E(a) splits every test set additively")
						test := b.TermAs[Set[A]]("t ∩ {x:A | ∃i:B. i ∈ insert(a, u) ∧ x ∈ E(i)}")
						testInside := b.Have(
							"the piece of t in the union over insert(a, u) lies in Ω",
							"t ∩ {x:A | ∃i:B. i ∈ insert(a, u) ∧ x ∈ E(i)} ⊆ Ω",
							BySets(inside))
						b.Show(
							"the piece in E(a) is the new term of the sum, the rest the sum over u",
							By(
								testInside,
								splits[1].At(test),
								pieces,
								earlier,
								previous,
								extended_nonneg_real.SumClauses,
								extended_nonneg_real.AddComm))
					}))))
	}),
})}
