package measure_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// RestrictMeasure — a measure restricted to a measurable set E is a measure
// on E, whose measurable sets are the traces U ∩ E of those of S. E being
// measurable, the traces are exactly the measurable subsets of E, so they
// form a sigma algebra on E; and cutting by E changes neither a measurable
// subset of E nor a union of them, so the restriction inherits the laws of μ.
var RestrictMeasure = restrictMeasureThm{family.Add(registry.ProofEntry{
	Name:    "RestrictMeasure",
	Reading: "E ∈ S is load-bearing because μ is unconstrained off S.",
	Key:     "prop_fe9f6e1a314dbe53",
	Build: family.Theorem(MeasureOn.Statement(Statement{
		Binders:    "∀E:set(A).",
		Hypotheses: []string{"E ∈ S"},
		Conclusion: "measure_on(E, image(λU:set(A). U ∩ E, S), restricted_measure(μ, E))",
		Abbrev: Abbrev{
			{Name: "trace", Text: "image(λU:set(A). U ∩ E, S)"},
		},
	}), func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal], measure Fact,
		E *Expr[Set[A]], measurableE Fact) {
		laws := a.Conjuncts(
			a.Unfolded(measure, MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")
		sigma, emptyMass, countable := laws[0], laws[1], laws[2]
		closure := a.Unfolded(sigma, sigma_algebra.SigmaAlgebraOnDef)
		operations := sigma_algebra.SigmaFiniteOperations.At(Ω, S)
		trace := a.Have(
			"E being measurable, the traces on E are exactly the measurable subsets of E",
			"∀u:set(A). u ∈ «trace» ⇔ u ∈ S ∧ u ⊆ E",
			Derive(func(b *Argument) {
				b.FixAs[Set[A]]("u")
				b.Iff()
				b.Forward(
					"a trace U ∩ E of a measurable U is measurable and lies in E",
					func(c *Argument, isTrace Fact) {
						c.Show(
							"an intersection of two measurable sets",
							By(measurableE, isTrace, sigma, set_basic.InImage, operations, set_order.InterSubset))
					})
				b.Backward(
					"a measurable subset u of E is its own trace u ∩ E",
					func(c *Argument, inside Fact) {
						c.Show(
							"u ∩ E is u",
							BySets(inside))
					})
			}))
		within := a.Have(
			"the traces lie in E",
			"«trace» ⊆ {u:set(A) | u ⊆ E}",
			BySets(trace))
		whole := a.Have(
			"E is its own trace",
			"E ∈ «trace»",
			By(trace, measurableE, set_order.SubsetRefl))
		complements := a.Have(
			"what a trace leaves of E is a trace",
			"∀u:set(A). u ∈ «trace» ⇒ E ∖ u ∈ «trace»",
			Derive(func(b *Argument) {
				b.FixAs[Set[A]]("u")
				isTrace := b.Assume()
				b.Show(
					"a difference of measurable sets, inside E",
					By(trace, measurableE, isTrace, sigma, operations, set_order.SubsetDiff))
			}))
		unions := a.Have(
			"the union of a sequence of traces is a trace",
			"∀a:(num → set(A)). (∀n:num. a(n) ∈ «trace») ⇒ ⋃image(a, 𝕌) ∈ «trace»",
			Derive(func(b *Argument) {
				b.FixAs[Fun[Nat, Set[A]]]("a")
				traces := b.Assume()
				terms := b.Have(
					"each a(n) is a measurable subset of E",
					"∀n:num. a(n) ∈ S ∧ a(n) ⊆ E",
					By(trace, traces))
				inside := b.Have(
					"so their union lies in E",
					"⋃image(a, 𝕌) ⊆ E",
					BySets(terms))
				b.Show(
					"and is measurable, a countable union of measurable sets",
					By(trace, terms, inside, closure))
			}))
		a.Show(
			"the traces form a sigma algebra on E, and the restriction inherits the laws of μ",
			MeasureOn.Intro(
				Case(
					"the traces form a sigma algebra on E",
					By(within, whole, complements, unions, sigma_algebra.SigmaAlgebraOnDef)),
				Case(
					"the empty set keeps measure zero",
					By(Normalized, emptyMass, RestrictMeasureDef, set_algebra.InterEmpty)),
				Case(
					"a disjoint sequence of traces is one of measurable subsets of E, which cutting by E leaves alone",
					Derive(func(b *Argument) {
						b.FixAs[Fun[Nat, Set[A]]]("a")
						given := b.Conjuncts(
							b.Assume(),
							"every a(n) is a trace",
							"the a(n) are disjoint")
						terms := b.Have(
							"each a(n) is a measurable subset of E",
							"∀n:num. a(n) ∈ S ∧ a(n) ⊆ E",
							By(trace, given[0]))
						uncut := b.Have(
							"cutting by E changes neither the a(n) nor their union",
							"⋃image(a, 𝕌) ∩ E = ⋃image(a, 𝕌) ∧ (∀n:num. a(n) ∩ E = a(n))",
							BySets(terms))
						b.Show(
							"so countable additivity of μ is that of the restriction",
							Simp(Fwd(RestrictMeasureDef), Fwd(uncut)),
							By(terms, given[1], countable))
					}))))
	}),
})}

// RestrictMeasureOnCarrier — a measure restricted to a measurable set E is
// still a measure on the whole carrier, U ↦ μ(U ∩ E) on S: the empty set
// cuts to the empty set, and cutting a disjoint sequence by E leaves a
// disjoint sequence of measurable sets whose union is the cut of the union.
var RestrictMeasureOnCarrier = restrictMeasureOnCarrierThm{family.Add(registry.ProofEntry{
	Name: "RestrictMeasureOnCarrier",
	Key:  "prop_c0e363dedefa6361",
	Build: family.Theorem(MeasureOn.Statement(Statement{
		Binders:    "∀E:set(A).",
		Hypotheses: []string{"E ∈ S"},
		Conclusion: "measure_on(Ω, S, restricted_measure(μ, E))",
	}), func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal], measure Fact,
		E *Expr[Set[A]], measurableE Fact) {
		laws := a.Conjuncts(
			a.Unfolded(measure, MeasureOn),
			"the measurable sets form a σ-algebra",
			"the empty set has mass zero",
			"the measure is countably additive")
		sigma, empty, countable := laws[0], laws[1], laws[2]
		restricted := a.TermAs[Fun[Set[A], ExtendedNonnegReal]]("restricted_measure(μ, E)")
		emptyCut := a.Have(
			"cutting the empty set leaves it empty",
			"∅ ∩ E = ∅",
			BySets())
		zero := a.Have(
			"the restricted mass of the empty set is zero",
			"restricted_measure(μ, E, ∅) = &0",
			By(Normalized, emptyCut, empty, RestrictMeasureDef.At(μ, E, a.TermAs[Set[A]]("∅"))))
		additive := a.Have(
			"countable additivity passes to the restriction",
			Statement{
				Binders:    "∀a:(num → set(A)).",
				Hypotheses: []string{"∀n:num. a(n) ∈ S", "∀i j:num. i ≠ j ⇒ a(i) ∩ a(j) = ∅"},
				Conclusion: "restricted_measure(μ, E, ⋃image(a, 𝕌)) = " +
					"extended_series(λn:num. restricted_measure(μ, E, a(n)))",
			},
			Derive(func(b *Argument) {
				b.FixAs[Fun[Nat, Set[A]]]("a")
				given := b.Conjuncts(
					b.Assume(),
					"all sets of the sequence are measurable",
					"the sets are pairwise disjoint")
				terms, disjoint := given[0], given[1]
				traces := b.Have(
					"intersecting each term with E gives a measurable set",
					"∀n:num. a(n) ∩ E ∈ S",
					Derive(func(c *Argument) {
						n := c.FixAs[Nat]("n")
						c.Show(
							"both factors are measurable",
							By(sigma, measurableE, terms.At(n), sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
					}))
				tracesDisjoint := b.Have(
					"the intersections are still pairwise disjoint",
					"∀i j:num. i ≠ j ⇒ (a(i) ∩ E) ∩ (a(j) ∩ E) = ∅",
					BySets(disjoint))
				distribution := b.Have(
					"intersection with E distributes over the union",
					"⋃image(a, 𝕌) ∩ E = ⋃image(λn:num. a(n) ∩ E, 𝕌)",
					BySets())
				b.Show(
					"the original measure adds over the disjoint intersections",
					Simp(Fwd(RestrictMeasureDef)),
					By(
						countable.At(b.TermAs[Fun[Nat, Set[A]]]("λn:num. a(n) ∩ E")),
						traces,
						tracesDisjoint,
						distribution))
			}))
		a.Show(
			"the same σ-algebra carries the restricted measure",
			By(sigma, zero, additive, MeasureOn.At(Ω, S, restricted)))
	}),
})}

// SubSigmaMeasure — a measure on S is a measure on any sub-sigma-algebra G:
// μ(∅) = 0 still, and a disjoint sequence of sets of G is one of S, so
// countable additivity holds for it.
var SubSigmaMeasure = subSigmaMeasureThm{family.Add(registry.ProofEntry{
	Name: "SubSigmaMeasure",
	Key:  "prop_6cc576bf805ff68a",
	Build: family.Theorem(MeasureOn.Statement(Statement{
		Binders:    "∀G:set(set(A)).",
		Hypotheses: []string{"sigma_algebra_on(Ω, G)", "G ⊆ S"},
		Conclusion: "measure_on(Ω, G, μ)",
	}), func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal], measure Fact,
		G *Expr[Set[Set[A]]], sigma, sub Fact) {
		laws := a.Conjuncts(
			a.Unfolded(measure, MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")
		a.Show(
			"the measure laws for S give those for G",
			MeasureOn.Intro(
				Case(
					"G is a sigma algebra on Ω",
					By(sigma)),
				Case(
					"the empty set has measure zero",
					By(laws[1])),
				Case(
					"a disjoint sequence of sets of G is one of S",
					By(sub, laws[2], set_basic.SubsetDef))))
	}),
})}

// PushforwardMeasure — a measurable map carries a measure forward: the
// pushforward measures a set of T by the preimage. The preimage of the empty
// set is empty, and the preimages of a disjoint sequence of T are a disjoint
// sequence of S whose union is the preimage of the union, so countable
// additivity of μ carries over.
var PushforwardMeasure = pushforwardMeasureThm{family.Add(registry.ProofEntry{
	Name: "PushforwardMeasure",
	Key:  "prop_3b7d5a5e91153afe",
	Build: family.Theorem(MeasureOn.Statement(Statement{
		Binders: "∀V:set(B). ∀T:set(set(B)). ∀f:(A → B).",

		Hypotheses: []string{
			"sigma_algebra_on(V, T)",
			"measurable_map(Ω, S, V, T, f)",
		},
		Conclusion: "measure_on(V, T, pushforward_measure(Ω, μ, f))",
	}), func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal], measure Fact,
		V *Expr[Set[B]], T *Expr[Set[Set[B]]], f *Arrow[A, B], sigma, measurable Fact) {
		laws := a.Conjuncts(
			a.Unfolded(measure, MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")
		emptyMass, countable := laws[1], laws[2]
		preimages := a.Conjuncts(
			a.Unfolded(measurable, measurable_space.MeasurableMapDef),
			"f maps Ω into V",
			"the preimage of a set of T is measurable")
		a.Show(
			"T is a sigma algebra, and the pushforward inherits the laws of μ through preimages",
			MeasureOn.Intro(
				Case(
					"T is a sigma algebra on V",
					By(sigma)),
				Case(
					"the preimage of the empty set is empty, of measure zero",
					Derive(func(b *Argument) {
						empty := b.Have(
							"no point is sent into the empty set",
							"preimage_on(Ω, f, ∅) = ∅",
							BySets())
						b.Show(
							"so the pushforward of ∅ is μ(∅)",
							Simp(Fwd(PushforwardMeasureDef), Fwd(empty)),
							By(emptyMass))
					})),
				Case(
					"the preimages of a disjoint sequence of T are a disjoint sequence of S",
					Derive(func(b *Argument) {
						b.FixAs[Fun[Nat, Set[B]]]("a")
						given := b.Conjuncts(
							b.Assume(),
							"every a(n) lies in T",
							"the a(n) are disjoint")
						terms := b.Have(
							"the preimages of the a(n) are measurable",
							"∀n:num. preimage_on(Ω, f, a(n)) ∈ S",
							By(given[0], preimages[1]))
						disjoint := b.Have(
							"and disjoint, as the a(n) are",
							"∀i j:num. i ≠ j ⇒ preimage_on(Ω, f, a(i)) ∩ preimage_on(Ω, f, a(j)) = ∅",
							BySets(given[1]))
						union := b.Have(
							"the preimage of the union is the union of the preimages",
							"preimage_on(Ω, f, ⋃image(a, 𝕌)) = ⋃image(λn:num. preimage_on(Ω, f, a(n)), 𝕌)",
							BySets())
						b.Show(
							"so countable additivity of μ is that of the pushforward",
							Simp(Fwd(PushforwardMeasureDef), Fwd(union)),
							By(terms, disjoint, countable.At(b.TermAs[Fun[Nat, Set[A]]]("λn:num. preimage_on(Ω, f, a(n))"))))
					}))))
	}),
})}

// DiscreteMeasure — weights on the points of Ω give a measure on all its
// subsets, a set measuring the supremum of the sums of the weights over its
// finite subsets. The subsets of Ω form a sigma algebra, and the empty set
// has only the empty sum. On a disjoint sequence a(n), a finite subset F of
// the union sums to the series of its pieces F ∩ a(n), each a finite subset
// of a(n); so the measure of the union is at most the series. Conversely the
// measure is superadditive on two disjoint sets — sums over finite subsets of
// each add up to the sum over their union — so each partial sum of the series
// is at most the measure of the union of the first sets, at most that of the
// whole union.
var DiscreteMeasure = discreteMeasureThm{family.Add(registry.ProofEntry{
	Name:    "DiscreteMeasure",
	Reading: "S is the full power set of Ω, and the values of w off Ω never enter.",
	Key:     "prop_5e22d31eafeceadc",
	Build: family.Sections(Statement{
		Binders:    "∀Ω:set(A). ∀w:(A → extended_nonneg_real).",
		Conclusion: "measure_on(Ω, {E:set(A) | E ⊆ Ω}, discrete_measure(Ω, w))",
		Abbrev: Abbrev{
			{Name: "sums", Text: "λU:set(A). " +
				"    {r:extended_nonneg_real | ∃F:set(A). finite(F) ∧ F ⊆ Ω ∩ U ∧ r = Σ_{x∈F} w(x)}"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		monotone := ctx.Lemma(Statement{
			Binders:    "∀Ω:set(A). ∀w:(A → extended_nonneg_real). ∀E D:set(A).",
			Hypotheses: []string{"E ⊆ D"},
			Conclusion: "discrete_measure(Ω, w, E) ≤ discrete_measure(Ω, w, D)",
		}, func(arg *Argument, Ω *Expr[Set[A]], w *Arrow[A, ExtendedNonnegReal], E, D *Expr[Set[A]],
			inside Fact) {
			arg.Do(Simp(Fwd(DiscreteMeasureDef)))
			fewer := arg.Have(
				"a finite subset of Ω ∩ E is one of Ω ∩ D",
				"«sums»(E) ⊆ «sums»(D)",
				BySets(inside))
			arg.Show(
				"so the supremum for E is at most that for D",
				By(fewer, extended_nonneg_real.SupMono))
		})
		superadditive := ctx.Lemma(Statement{
			Binders:    "∀Ω:set(A). ∀w:(A → extended_nonneg_real). ∀E D:set(A).",
			Hypotheses: []string{"E ∩ D = ∅"},
			Conclusion: "discrete_measure(Ω, w, E) + discrete_measure(Ω, w, D) ≤ discrete_measure(Ω, w, E ∪ D)",
		}, func(arg *Argument, Ω *Expr[Set[A]], w *Arrow[A, ExtendedNonnegReal], E, D *Expr[Set[A]],
			apart Fact) {
			whole := arg.TermAs[ExtendedNonnegReal]("extended_sup(«sums»(E ∪ D))")
			pairs := arg.Have(
				"a sum over a finite subset of Ω ∩ E and one over a finite subset of Ω "+
					"∩ D add up to the sum over their union, a finite subset of Ω ∩ (E ∪ D)",
				"∀y z:extended_nonneg_real. y ∈ «sums»(E) ∧ z ∈ «sums»(D) ⇒ y + z ≤ extended_sup(«sums»(E ∪ D))",
				Derive(func(b *Argument) {
					b.FixAs[ExtendedNonnegReal]("y")
					b.FixAs[ExtendedNonnegReal]("z")
					members := b.Conjuncts(
						b.Assume(),
						"y is a sum over a finite subset of Ω ∩ E",
						"z is a sum over a finite subset of Ω ∩ D")
					_, first := b.UnpackAs[Set[A]](members[0], "F")
					_, second := b.UnpackAs[Set[A]](members[1], "G")
					left := b.Conjuncts(
						first,
						"F is finite",
						"F lies in Ω ∩ E",
						"y is the sum over F")
					right := b.Conjuncts(
						second,
						"G is finite",
						"G lies in Ω ∩ D",
						"z is the sum over G")
					placed := b.Have(
						"F and G are disjoint, and their union lies in Ω ∩ (E ∪ D)",
						"F ∩ G = ∅ ∧ F ∪ G ⊆ Ω ∩ (E ∪ D)",
						BySets(apart, left[1], right[1]))
					joined := b.Have(
						"so the sum over the finite set F ∪ G is the sum over F plus the sum over G",
						"Σ_{x∈F ∪ G} w(x) = Σ_{x∈F} w(x) + Σ_{x∈G} w(x) ∧ finite(F ∪ G)",
						By(
							Normalized,
							placed,
							left[0],
							right[0],
							set_basic.DisjointDef,
							monoidal.Union.Read(extended_nonneg_real.MonoidalAdd),
							extended_nonneg_real.ExtendedSumDef,
							finite_set.FiniteUnionImp))
					b.Show(
						"and that sum is among those for E ∪ D",
						By(left[2], right[2], joined, placed, extended_nonneg_real.SupUpper))
				}))
			nonempty := arg.Have(
				"the empty set gives the sum 0, so neither set of sums is empty",
				"«sums»(E) ≠ ∅ ∧ «sums»(D) ≠ ∅",
				Derive(func(b *Argument) {
					zero := b.Have(
						"0 is the sum over the empty set, a finite subset of both",
						"extended_of_real(&0) ∈ «sums»(E) ∧ extended_of_real(&0) ∈ «sums»(D)",
						By(finite_set.FiniteRules, set_order.EmptySubset, extended_nonneg_real.SumClauses))
					b.Show(
						"a set with a member is not empty",
						BySets(zero))
				}))
			oneSide := arg.Have(
				"the supremum for E plus any sum for D is at most the supremum for E ∪ D",
				Statement{
					Binders:    "∀z:extended_nonneg_real.",
					Hypotheses: []string{"z ∈ «sums»(D)"},
					Conclusion: "extended_sup(«sums»(E)) + z ≤ extended_sup(«sums»(E ∪ D))",
				},
				Derive(func(b *Argument) {
					z := b.FixAs[ExtendedNonnegReal]("z")
					member := b.Assume()
					each := b.Have(
						"each sum for E plus z is at most the supremum for E ∪ D",
						"∀y:extended_nonneg_real. y ∈ «sums»(E) ⇒ y + z ≤ extended_sup(«sums»(E ∪ D))",
						By(member, pairs))
					b.Show(
						"so is the supremum for E plus z",
						By(
							nonempty,
							each,
							extended_nonneg_real.SupAddLe.At(b.TermAs[Set[ExtendedNonnegReal]]("«sums»(E)"), z, whole)))
				}))
			swapped := arg.Have(
				"so each sum for D plus the supremum for E is",
				Statement{
					Binders:    "∀z:extended_nonneg_real.",
					Hypotheses: []string{"z ∈ «sums»(D)"},
					Conclusion: "z + extended_sup(«sums»(E)) ≤ extended_sup(«sums»(E ∪ D))",
				},
				By(oneSide, extended_nonneg_real.AddComm))
			arg.Do(Simp(Fwd(DiscreteMeasureDef)))
			arg.Show(
				"and so is the supremum for E plus the supremum for D",
				By(
					nonempty,
					swapped,
					extended_nonneg_real.SupAddLe.At(
						arg.TermAs[Set[ExtendedNonnegReal]]("«sums»(D)"),
						arg.TermAs[ExtendedNonnegReal]("extended_sup(«sums»(E))"),
						whole),
					extended_nonneg_real.AddComm))
		})
		partition := ctx.Lemma(Statement{
			Binders: "∀w:(A → extended_nonneg_real). ∀a:(num → set(A)). ∀F:set(A).",
			Hypotheses: []string{
				"finite(F)",
				"F ⊆ ⋃image(a, 𝕌)",
				"∀i j:num. i ≠ j ⇒ a(i) ∩ a(j) = ∅",
			},
			Conclusion: "Σ_{x∈F} w(x) = extended_series(λn:num. Σ_{x∈F ∩ a(n)} w(x))",
		}, func(arg *Argument, w *Arrow[A, ExtendedNonnegReal], a *Arrow[Nat, Set[A]], F *Expr[Set[A]],
			finite, covered, disjoint Fact) {
			arg.Show(
				"by induction over the finite set F",
				ByInduction(finite_set.FiniteInductFresh, finite, Generalizing(covered),
					Case(
						"the empty set sums to 0, and so does each of its pieces",
						Derive(func(b *Argument) {
							b.Assume()
							pieces := b.Have(
								"every piece of the empty set is empty",
								"∀n:num. ∅ ∩ a(n) = ∅",
								BySets())
							b.Show(
								"a series of zeros",
								Simp(Fwd(pieces), Fwd(extended_nonneg_real.SumClauses)),
								By(extended_nonneg_real.SeriesZero))
						})),
					Case(
						"a new point p lies in exactly one a(m), and joins only the piece there",
						Derive(func(b *Argument) {
							p := b.FixAs[A]("p")
							b.FixAs[Set[A]]("u")
							previous := b.Conjuncts(
								b.Assume(),
								"the sum over u splits over its pieces once u lies in the union",
								"p is new",
								"u is finite")
							inserted := b.Assume()
							before := b.Have(
								"u lies in the union, so its sum splits over its pieces",
								"Σ_{x∈u} w(x) = extended_series(λn:num. Σ_{x∈u ∩ a(n)} w(x))",
								By(
									previous[0],
									b.Have(
										"u lies in the union",
										"u ⊆ ⋃image(a, 𝕌)",
										BySets(inserted))))
							m, home := b.ObtainAs[Nat](
								"p lies in some a(m)",
								"∃m:num. p ∈ a(m)",
								BySets(inserted))
							pieces := b.Have(
								"adding p changes only the piece at m, by w(p)",
								"∀n:num. Σ_{x∈insert(p, u) ∩ a(n)} w(x) = Σ_{x∈u ∩ a(n)} w(x) + COND(n = m, w(p), &0)",
								Derive(func(c *Argument) {
									n := c.FixAs[Nat]("n")
									c.Cases(c.Term("n = m"))
									c.When(
										"at m the piece gains p, new to it",
										func(d *Argument, same Fact) {
											grown := d.Have(
												"the piece at m is the piece of u with p inserted",
												"insert(p, u) ∩ a(n) = insert(p, u ∩ a(n)) ∧ p ∉ u ∩ a(n) ∧ u ∩ a(n) ⊆ u",
												BySets(same, home, previous[1]))
											finitePiece := d.Have(
												"the piece of u is finite",
												"finite(u ∩ a(n))",
												By(grown, previous[2], finite_set.FiniteSubset))
											gained := d.Have(
												"inserting the new point p into a finite set adds w(p) to its sum",
												"Σ_{x∈insert(p, u ∩ a(n))} w(x) = w(p) + Σ_{x∈u ∩ a(n)} w(x)",
												By(Normalized, finitePiece, grown, extended_nonneg_real.SumClauses))
											d.Show(
												"so the sum over the piece gains w(p)",
												By(Normalized, same, grown, gained, extended_nonneg_real.AddComm))
										})
									c.Otherwise(
										"elsewhere p is not in the piece, a(n) missing a(m)",
										func(d *Argument, other Fact) {
											apart := d.Have(
												"the piece is the piece of u",
												"insert(p, u) ∩ a(n) = u ∩ a(n)",
												BySets(other, home, disjoint.At(m, n)))
											d.Show(
												"and its sum is unchanged",
												By(other, apart, extended_nonneg_real.AddZero))
										})
								}))
							b.Show(
								"the series gains w(p), which is what the sum gains",
								Simp(Fwd(pieces)),
								By(
									before,
									previous[1],
									previous[2],
									extended_nonneg_real.SeriesAdd.At(
										b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. Σ_{x∈u ∩ a(n)} w(x)"),
										b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. COND(n = m, w(p), &0)")),
									extended_nonneg_real.SeriesSingleton.At(w.Apply(p), m),
									extended_nonneg_real.SumClauses,
									extended_nonneg_real.AddComm))
						}))))
		})
		return ctx.Theorem(headline, func(arg *Argument, Ω *Expr[Set[A]], w *Arrow[A, ExtendedNonnegReal]) {
			arg.Show(
				"the subsets of Ω form a sigma algebra, and the discrete measure satisfies the measure laws there",
				MeasureOn.Intro(
					Case(
						"the subsets of Ω form a sigma algebra",
						Simp(Fwd(sigma_algebra.SigmaAlgebraOnDef)),
						BySets()),
					Case(
						"the empty set has only the empty sum",
						Derive(func(b *Argument) {
							bounded := b.Have(
								"a sum over a finite subset of Ω ∩ ∅ is the sum over ∅, which is 0",
								"∀y:extended_nonneg_real. y ∈ «sums»(∅) ⇒ y ≤ &0",
								Derive(func(c *Argument) {
									c.FixAs[ExtendedNonnegReal]("y")
									_, member := c.UnpackAs[Set[A]](c.Assume(), "F")
									parts := c.Conjuncts(
										member,
										"F is finite",
										"F lies in Ω ∩ ∅",
										"y is the sum over F")
									empty := c.Have(
										"F is empty",
										"F = ∅",
										BySets(parts[1]))
									c.Show(
										"so y is 0",
										By(parts[2], empty, extended_nonneg_real.SumClauses, extended_nonneg_real.LeRefl))
								}))
							b.Do(Simp(Fwd(DiscreteMeasureDef)))
							b.Show(
								"so the supremum is 0",
								By(
									bounded,
									extended_nonneg_real.SupLeast,
									extended_nonneg_real.ZeroLe,
									extended_nonneg_real.LeAntisym))
						})),
					Case(
						"the measure of a disjoint union is the series of the measures",
						Derive(func(b *Argument) {
							a := b.FixAs[Fun[Nat, Set[A]]]("a")
							given := b.Conjuncts(
								b.Assume(),
								"every a(n) is a subset of Ω",
								"the a(n) are disjoint")
							union := b.TermAs[Set[A]]("⋃image(a, 𝕌)")
							bound := b.Have(
								"a sum over a finite subset of Ω ∩ ⋃a is the series of the "+
									"sums over its pieces, each at most the measure of its a(n)",
								Statement{
									Binders:    "∀y:extended_nonneg_real.",
									Hypotheses: []string{"y ∈ «sums»(⋃image(a, 𝕌))"},
									Conclusion: "y ≤ extended_series(λn:num. discrete_measure(Ω, w, a(n)))",
								},
								Derive(func(c *Argument) {
									c.FixAs[ExtendedNonnegReal]("y")
									F, member := c.UnpackAs[Set[A]](c.Assume(), "F")
									parts := c.Conjuncts(
										member,
										"F is finite",
										"F lies in Ω and the union",
										"y is the sum over F")
									covered := c.Have(
										"F lies in the union",
										"F ⊆ ⋃image(a, 𝕌)",
										BySets(parts[1]))
									pieces := c.Have(
										"each piece F ∩ a(n), a finite subset of Ω ∩ a(n), sums to at most the measure of a(n)",
										"∀n:num. Σ_{x∈F ∩ a(n)} w(x) ≤ discrete_measure(Ω, w, a(n))",
										Derive(func(d *Argument) {
											d.FixAs[Nat]("n")
											inside := d.Have(
												"the piece lies in F and in Ω ∩ a(n)",
												"F ∩ a(n) ⊆ F ∧ F ∩ a(n) ⊆ Ω ∩ a(n)",
												BySets(parts[1]))
											finitePiece := d.Have(
												"so it is finite",
												"finite(F ∩ a(n))",
												By(inside, parts[0], finite_set.FiniteSubset))
											d.Show(
												"its sum is among those for a(n)",
												By(
													inside,
													finitePiece,
													DiscreteMeasureDef.At(Ω, w, d.TermAs[Set[A]]("a(n)")),
													extended_nonneg_real.SupUpper))
										}))
									c.Show(
										"so y, the series of the sums over the pieces, is at most the series of the measures",
										By(
											parts[2],
											parts[0],
											covered,
											given[1],
											At(partition, w, a, F),
											pieces,
											extended_nonneg_real.SeriesMono.At(
												c.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. Σ_{x∈F ∩ a(n)} w(x)"),
												c.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. discrete_measure(Ω, w, a(n))"))))
								}))
							upper := b.Have(
								"so the measure of the union is at most the series",
								"discrete_measure(Ω, w, ⋃image(a, 𝕌)) ≤ extended_series(λn:num. discrete_measure(Ω, w, a(n)))",
								By(DiscreteMeasureDef.At(Ω, w, union), bound, extended_nonneg_real.SupLeast))
							segments := b.Have(
								"the measures of the first sets add up to at most the measure of their union",
								"∀N:num. Σ_{n∈0 .. N} discrete_measure(Ω, w, a(n)) ≤ discrete_measure(Ω, w, ⋃image(a, 0 .. N))",
								Derive(func(c *Argument) {
									c.Induct("N")
									c.Base(
										"the first set is the union of the first sets",
										func(d *Argument) {
											first := d.Have(
												"the union of the sets up to 0 is a(0)",
												"⋃image(a, 0 .. 0) = a(0)",
												BySets(num_segment.MembershipFromZero, nat_order.LessEqZeroClause))
											d.Show(
												"so the measures agree",
												By(first, extended_nonneg_real.SumSegmentZero, extended_nonneg_real.LeRefl))
										})
									c.Step(
										"the next set is disjoint from the union so far, and superadditivity adds its measure",
										func(d *Argument, ih Fact) {
											d.Do(Simp(Fwd(nat_arith.Add1)))
											counting := d.Have(
												"an index up to N + 1 is one up to N or N + 1 itself, and one up to N is not N + 1",
												"∀m:num. (m ≤ N + 1 ⇔ m ≤ N ∨ m = N + 1) ∧ (m ≤ N ⇒ m ≠ N + 1)",
												ByArith())
											grown := d.Have(
												"the union up to N + 1 is the union up to N together with a(N + 1), which it misses",
												"⋃image(a, 0 .. N + 1) = ⋃image(a, 0 .. N) ∪ a(N + 1) ∧ ⋃image(a, 0 .. N) ∩ a(N + 1) = ∅",
												BySets(counting, num_segment.MembershipFromZero, given[1]))
											partialSum := d.TermAs[ExtendedNonnegReal]("Σ_{n∈0 .. N} discrete_measure(Ω, w, a(n))")
											firstUnion := d.TermAs[ExtendedNonnegReal]("discrete_measure(Ω, w, ⋃image(a, 0 .. N))")
											next := d.TermAs[ExtendedNonnegReal]("discrete_measure(Ω, w, a(N + 1))")
											raised := d.Have(
												"adding the measure of a(N + 1) keeps the bound so far",
												"Σ_{n∈0 .. N} discrete_measure(Ω, w, a(n)) + discrete_measure(Ω, w, a(N + 1)) ≤ "+
													"discrete_measure(Ω, w, ⋃image(a, 0 .. N)) + discrete_measure(Ω, w, a(N + 1))",
												By(ih, extended_nonneg_real.AddLeMono.At(partialSum, firstUnion, next)))
											joined := d.Have(
												"and superadditivity bounds that by the measure of the union up to N + 1",
												"discrete_measure(Ω, w, ⋃image(a, 0 .. N)) + discrete_measure(Ω, w, a(N + 1)) ≤ "+
													"discrete_measure(Ω, w, ⋃image(a, 0 .. N + 1))",
												By(
													grown,
													At(superadditive, Ω, w,
														d.TermAs[Set[A]]("⋃image(a, 0 .. N)"),
														d.TermAs[Set[A]]("a(N + 1)"))))
											d.Show(
												"so the partial sum through N + 1 is at most its measure",
												By(
													extended_nonneg_real.SumSegmentPeel.At(
														d.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. discrete_measure(Ω, w, a(n))"),
														d.TermAs[Nat]("N")),
													raised,
													joined,
													extended_nonneg_real.LeTrans))
										})
								}))
							partial := b.Have(
								"so each partial sum of the series is at most the "+
									"measure of the whole union, which holds every first union",
								"∀N:num. Σ_{n∈0 .. N} discrete_measure(Ω, w, a(n)) ≤ discrete_measure(Ω, w, ⋃image(a, 𝕌))",
								Derive(func(c *Argument) {
									N := c.FixAs[Nat]("N")
									within := c.Have(
										"the first sets lie in the union",
										"⋃image(a, 0 .. N) ⊆ ⋃image(a, 𝕌)",
										BySets())
									c.Show(
										"chain the two bounds",
										By(
											segments.At(N),
											within,
											At(monotone, Ω, w, c.TermAs[Set[A]]("⋃image(a, 0 .. N)"), union),
											extended_nonneg_real.LeTrans))
								}))
							lower := b.Have(
								"and so is the series",
								"extended_series(λn:num. discrete_measure(Ω, w, a(n))) ≤ discrete_measure(Ω, w, ⋃image(a, 𝕌))",
								By(partial, extended_nonneg_real.SeriesLeast))
							b.Show(
								"the two bounds meet",
								By(upper, lower, extended_nonneg_real.LeAntisym))
						}))))
		})
	}),
})}
