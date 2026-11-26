package nat_sum

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// EvenOddSubsetCounts — a nonempty finite set has equally many even and odd
// subsets. Toggling a chosen point exchanges the two families and is its
// own inverse.
var EvenOddSubsetCounts = evenOddSubsetCountsThm{family.Add(registry.ProofEntry{
	Name: "EvenOddSubsetCounts",
	Key:  "prop_c42a5035b3b57005",
	Build: family.Sections(Statement{
		Binders:    "∀s:set(A).",
		Hypotheses: []string{"finite(s)", "s ≠ ∅"},
		Conclusion: "card(«evenSubsets»(s)) = card(«oddSubsets»(s))",
		Abbrev: Abbrev{
			{Name: "toggle", Text: "λx:A. λv:set(A). COND(x ∈ v, delete(v, x), insert(x, v))"},
			{Name: "evenSubsets", Text: "λL:set(A). {t:set(A) | t ⊆ L ∧ nat_even(card(t))}"},
			{Name: "oddSubsets", Text: "λL:set(A). {t:set(A) | t ⊆ L ∧ nat_odd(card(t))}"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		toggleSwitchesParity := ctx.Lemma(Statement{
			Binders:    "∀s:set(A). ∀x:A. ∀t:set(A).",
			Hypotheses: []string{"finite(s)", "x ∈ s", "t ⊆ s"},
			Conclusion: "«toggle»(x, t) ⊆ s ∧ " +
				"«toggle»(x, «toggle»(x, t)) = t ∧ " +
				"((nat_even(card(«toggle»(x, t))) ⇔ nat_odd(card(t))) ∧ " +
				"    (nat_odd(card(«toggle»(x, t))) ⇔ nat_even(card(t))))",
		}, func(a *Argument, s *Expr[Set[A]], x *Expr[A], t *Expr[Set[A]], finiteS, inS, within Fact) {
			finiteT := a.Have(
				"t is finite as a subset of s",
				"finite(t)",
				By(finiteS, within, finite_set.FiniteSubset.At(t, s)))
			a.Cases(a.Term("x ∈ t"))
			a.When(
				"if t contains x, toggling removes it",
				func(b *Argument, contains Fact) {
					removed := b.Have(
						"toggling deletes x",
						"«toggle»(x, t) = delete(t, x)",
						By(contains))
					absent := b.Have(
						"the deleted point is absent",
						"x ∉ delete(t, x)",
						BySets())
					b.Do(SplitConj(
						Case(
							"the smaller set stays in s and adding x back restores t",
							BySets(removed, contains, within)),
						Case(
							"removing one point changes the parity",
							Derive(func(c *Argument) {
								smaller := c.Have(
									"t has one more point than the set with x deleted",
									"card(t) = suc(card(delete(t, x)))",
									By(
										Normalized,
										finiteT,
										absent,
										contains,
										set_algebra.InsertDelete.At(t, x),
										finite_set.FiniteDelete.At(t, x),
										cardinality.CardClauses))
								c.Show(
									"the two sizes have opposite parity",
									ByArith(removed, smaller))
							}))))
				})
			a.Otherwise(
				"if t misses x, toggling adds it",
				func(b *Argument, absent Fact) {
					added := b.Have(
						"toggling inserts x",
						"«toggle»(x, t) = insert(x, t)",
						By(absent))
					b.Do(SplitConj(
						Case(
							"the enlarged set stays in s and deleting x again restores t",
							BySets(added, inS, within, set_algebra.DeleteInsert.At(t, x, x))),
						Case(
							"adding one point changes the parity",
							ByArith(finiteT, absent, added, cardinality.CardClauses))))
				})
		})

		return ctx.Theorem(headline, func(a *Argument, s *Expr[Set[A]], finiteS, nonempty Fact) {
			x, inS := a.ObtainAs[A](
				"choose a point of s",
				"∃x:A. x ∈ s",
				By(nonempty, set_basic.MemberNotEmpty.At(s)))
			toOdd := a.Have(
				"toggling an even subset gives an odd subset, and toggling again restores it",
				Statement{
					Binders:    "∀t:set(A).",
					Hypotheses: []string{"t ∈ «evenSubsets»(s)"},
					Conclusion: "«toggle»(x, t) ∈ «oddSubsets»(s) ∧ «toggle»(x, «toggle»(x, t)) = t",
				},
				Derive(func(b *Argument) {
					t := b.FixAs[Set[A]]("t")
					even := b.Assume()
					b.Show(
						"toggling reverses parity",
						BySets(inS, even, finiteS, At(toggleSwitchesParity, s, x, t)))
				}))
			toEven := a.Have(
				"toggling an odd subset gives an even subset, and toggling again restores it",
				Statement{
					Binders:    "∀t:set(A).",
					Hypotheses: []string{"t ∈ «oddSubsets»(s)"},
					Conclusion: "«toggle»(x, t) ∈ «evenSubsets»(s) ∧ «toggle»(x, «toggle»(x, t)) = t",
				},
				Derive(func(b *Argument) {
					t := b.FixAs[Set[A]]("t")
					odd := b.Assume()
					b.Show(
						"toggling reverses parity",
						BySets(inS, odd, finiteS, At(toggleSwitchesParity, s, x, t)))
				}))
			evens := a.TermAs[Set[Set[A]]]("«evenSubsets»(s)")
			odds := a.TermAs[Set[Set[A]]]("«oddSubsets»(s)")
			toggle := a.TermAs[Fun[Set[A], Set[A]]]("«toggle»(x)")
			evensFinite := a.Have(
				"a finite set has only finitely many even subsets",
				"finite(«evenSubsets»(s))",
				By(
					finiteS,
					finite_set.FiniteRestrictedSubsets.At(a.TermAs[Set[Set[A]]]("λt:set(A). nat_even(card(t))"), s)))
			a.Show(
				"toggling, its own inverse, matches them with the odd subsets, so the two count the same",
				By(toOdd, toEven, evensFinite, cardinality.MutualInversesCard.At(evens, odds, toggle, toggle)))
		})
	}),
})}

// InclusionExclusion — the even intersection counts balance the odd
// intersection counts plus the uncovered points, those of U outside the
// union. For a point covered by some set, the index subsets whose
// intersections contain it come in opposite-parity pairs. An uncovered
// point is counted only by the empty index subset.
var InclusionExclusion = inclusionExclusionThm{family.Add(registry.ProofEntry{
	Name: "InclusionExclusion",
	Key:  "prop_f7c91862966bb83a",
	Build: family.Sections(Statement{
		Binders:    "∀U:set(A). ∀I:set(B). ∀F:(B → set(A)).",
		Hypotheses: []string{"finite(U)", "finite(I)"},
		Conclusion: "Σ_{J∈«evenSubsets»(I)} card(«intersections»(J)) = " +
			"card(«uncovered») + Σ_{J∈«oddSubsets»(I)} card(«intersections»(J))",
		Abbrev: Abbrev{
			{Name: "indices", Text: "λx:A. {i:B | i ∈ I ∧ x ∈ F(i)}"},
			{Name: "subsetIncidence", Text: "λJ:set(B). λx:A. J ⊆ «indices»(x)"},
			{Name: "intersections", Text: "λJ:set(B). U ∩ ⋂image(F, J)"},
			{Name: "subsetsWhere", Text: "λL:set(B). λP:(set(B) → bool). {J:set(B) | J ⊆ L ∧ P(J)}"},
			{Name: "evenSubsets", Text: "λL:set(B). {t:set(B) | t ⊆ L ∧ nat_even(card(t))}"},
			{Name: "oddSubsets", Text: "λL:set(B). {t:set(B) | t ⊆ L ∧ nat_odd(card(t))}"},
			{Name: "uncovered", Text: "U ∖ ⋃image(F, I)"},
			{Name: "indicator", Text: "λx:A. COND(x ∉ ⋃image(F, I), 1, 0)"},
			{Name: "evenFibre", Text: "λx:A. card(«evenSubsets»(«indices»(x)))"},
			{Name: "oddFibre", Text: "λx:A. card(«oddSubsets»(«indices»(x)))"},
			{Name: "pointsInIntersection", Text: "λJ:set(B). {x:A | x ∈ U ∧ «subsetIncidence»(J, x)}"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		countIntersections := ctx.Lemma(Statement{
			Binders:    "∀U:set(A). ∀I:set(B). ∀F:(B → set(A)). ∀P:(set(B) → bool).",
			Hypotheses: []string{"finite(U)", "finite(I)"},
			Conclusion: "Σ_{J∈«subsetsWhere»(I, P)} card(«intersections»(J)) = " +
				"Σ_{x∈U} card(«subsetsWhere»(«indices»(x), P))",
		}, func(a *Argument, U *Expr[Set[A]], I *Expr[Set[B]], F *Arrow[B, Set[A]],
			P *Expr[Set[Set[B]]], finiteU, finiteI Fact) {
			selected := a.TermAs[Set[Set[B]]]("«subsetsWhere»(I, P)")
			finiteSelected := a.Have(
				"a finite index set has only finitely many selected subsets",
				"finite(«subsetsWhere»(I, P))",
				By(finiteI, finite_set.FiniteRestrictedSubsets.At(P, I)))
			points := a.Have(
				"the points incident to an index subset are its intersection inside U",
				"∀J:set(B). J ⊆ I ⇒ «pointsInIntersection»(J) = «intersections»(J)",
				Derive(func(b *Argument) {
					J := b.FixAs[Set[B]]("J")
					within := b.Assume()
					inEvery := b.Have(
						"intersection membership means membership in every set indexed by J",
						"∀x:A. x ∈ ⋂image(F, J) ⇔ (∀i:B. i ∈ J ⇒ x ∈ F(i))",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							c.Show(
								"read the intersection over the image of J",
								By(
									set_basic.InInters.At(c.TermAs[Set[Set[A]]]("image(F, J)"), x),
									set_image.ForallInImage.At(F, J, c.TermAs[Set[Set[A]]]("λS:set(A). x ∈ S"))))
						}))
					samePoints := b.Have(
						"the two sets have the same points",
						"∀x:A. x ∈ «pointsInIntersection»(J) ⇔ x ∈ «intersections»(J)",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							c.Show(
								"each index of J belongs to I",
								Simp(Fwd(set_basic.InInter)),
								inEvery.At(x).Rw(),
								BySets(within))
						}))
					b.Show(
						"so the two sets are equal",
						By(
							samePoints,
							set_basic.Extension.At(
								b.TermAs[Set[A]]("«pointsInIntersection»(J)"),
								b.TermAs[Set[A]]("«intersections»(J)"))))
				}))
			fibres := a.Have(
				"an index subset incident to x is a selected subset of the indices covering x",
				"∀x:A. "+
					"    {J:set(B) | J ∈ «subsetsWhere»(I, P) ∧ «subsetIncidence»(J, x)} = "+
					"    «subsetsWhere»(«indices»(x), P)",
				a.ForEach(func(x *Expr[A]) Action { return BySets() }))
			intersectionCounts := a.Have(
				"each selected intersection has its incidence count",
				"∀J:set(B). J ∈ «subsetsWhere»(I, P) ⇒ card(«intersections»(J)) = card(«pointsInIntersection»(J))",
				Derive(func(b *Argument) {
					J := b.FixAs[Set[B]]("J")
					chosen := b.Assume()
					b.Show(
						"a selected index subset lies inside I",
						By(chosen, points.At(J)))
				}))
			a.Show(
				"count the incidences first by index subsets and then by points of U",
				Simp(Rev(fibres)),
				By(
					finiteSelected,
					intersectionCounts,
					finiteU,
					Congruence.At(selected,
						a.TermAs[Fun[Set[B], Nat]]("λJ:set(B). card(«intersections»(J))"),
						a.TermAs[Fun[Set[B], Nat]]("λJ:set(B). card(«pointsInIntersection»(J))")),
					DoubleCounting.At(selected, U, a.TermAs[Fun2[Set[B], A, Bool]]("«subsetIncidence»"))))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			U *Expr[Set[A]],
			I *Expr[Set[B]],
			F *Arrow[B, Set[A]],
			finiteU, finiteI Fact,
		) {
			uncoveredIff := a.Have(
				"a point is uncovered exactly when no index covers it",
				"∀x:A. x ∉ ⋃image(F, I) ⇔ «indices»(x) = ∅",
				a.ForEach(func(x *Expr[A]) Action { return BySets() }))
			balance := a.Have(
				"at each point, the even count is the odd count plus the indicator of being uncovered",
				"∀x:A. «evenFibre»(x) = «indicator»(x) + «oddFibre»(x)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					b.Cases(b.Term("x ∉ ⋃image(F, I)"))
					b.When(
						"at an uncovered point, only the empty index subset contributes",
						func(c *Argument, uncovered Fact) {
							noIndex := c.Have(
								"no index covers x",
								"«indices»(x) = ∅",
								By(uncovered, uncoveredIff.At(x)))
							emptyEven := c.Have(
								"the empty index subset has even size",
								"nat_even(card(∅⟨A:B⟩)) ∧ ¬nat_odd(card(∅⟨A:B⟩))",
								ByArith(cardinality.CardClauses.Inst[B]()))
							families := c.Have(
								"the even fibre is a singleton and the odd fibre is empty",
								"«evenSubsets»(«indices»(x)) = {∅⟨A:B⟩} ∧ «oddSubsets»(«indices»(x)) = ∅",
								BySets(noIndex, emptyEven))
							c.Show(
								"the even count and the indicator are both one",
								ByArith(
									uncovered,
									families,
									cardinality.CardSing.At(c.TermAs[Set[B]]("∅")),
									cardinality.CardClauses.Inst[Set[B]]()))
						})
					b.Otherwise(
						"at a covered point, the even and odd index subsets balance",
						func(c *Argument, covered Fact) {
							nonempty := c.Have(
								"some index covers x",
								"«indices»(x) ≠ ∅",
								By(uncoveredIff.At(x), covered))
							finite := c.Have(
								"only finitely many indices cover x",
								"finite(«indices»(x))",
								By(finiteI, finite_set.FiniteRestrict.At(I, c.TermAs[Set[B]]("λi:B. x ∈ F(i)"))))
							c.Show(
								"the two counts agree and the indicator is zero",
								ByArith(finite, nonempty, covered, EvenOddSubsetCounts.At(c.TermAs[Set[B]]("«indices»(x)"))))
						})
				}))
			evenSum := a.Have(
				"count the even intersections by points",
				"Σ_{J∈«evenSubsets»(I)} card(«intersections»(J)) = Σ_{x∈U} «evenFibre»(x)",
				By(
					finiteU,
					finiteI,
					At(countIntersections, U, I, F,
						a.TermAs[Set[Set[B]]]("λJ:set(B). nat_even(card(J))"))))
			oddSum := a.Have(
				"count the odd intersections by points",
				"Σ_{J∈«oddSubsets»(I)} card(«intersections»(J)) = Σ_{x∈U} «oddFibre»(x)",
				By(
					finiteU,
					finiteI,
					At(countIntersections, U, I, F,
						a.TermAs[Set[Set[B]]]("λJ:set(B). nat_odd(card(J))"))))
			uncoveredCount := a.Have(
				"the uncovered points, counted by their indicators",
				"card(«uncovered») = Σ_{x∈U} «indicator»(x)",
				Derive(func(b *Argument) {
					restricted := b.Have(
						"restrict U to its uncovered points",
						"«uncovered» = {x:A | x ∈ U ∧ x ∉ ⋃image(F, I)}",
						BySets())
					b.Show(
						"sum the indicator over U",
						By(restricted, finiteU, CountByIndicator.At(U, b.TermAs[Set[A]]("λx:A. x ∉ ⋃image(F, I)"))))
				}))
			a.Show(
				"sum the pointwise balance over U",
				By(
					balance,
					uncoveredCount,
					evenSum,
					oddSum,
					finiteU,
					Congruence.At(U, a.TermAs[Fun[A, Nat]]("«evenFibre»"),
						a.TermAs[Fun[A, Nat]]("λx:A. «indicator»(x) + «oddFibre»(x)")),
					Add.At(a.TermAs[Fun[A, Nat]]("«indicator»"), a.TermAs[Fun[A, Nat]]("«oddFibre»"), U)))
		})
	}),
})}
