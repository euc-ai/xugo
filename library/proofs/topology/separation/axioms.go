// axioms.go — the separation axioms below normality and how they stand to
// each other: of two distinct points some open set holds exactly one
// (T0), each has an open neighbourhood missing the other (T1), the two
// lie in disjoint open sets (Hausdorff, defined with the space in
// topological_space); a closed set and a point outside it lie in
// disjoint open sets (regular). T1 is the closedness of points; regular
// is the existence, inside every open neighbourhood of a point, of an
// open one whose closure is still inside. A subspace inherits each.

package separation

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// T0 and T1
// ---------------------------------------------------------------------------

// HausdorffImpT1 — a Hausdorff space is T1: of the two disjoint open
// sets about two distinct points, the one about the first misses the
// second. No axiom enters, so the family is spelled.
var HausdorffImpT1 = hausdorffImpT1Thm{family.Add(registry.ProofEntry{
	Name: "HausdorffImpT1",
	Key:  "prop_a92b6b8b3cc118d0",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)).",
		Hypotheses: []string{
			"hausdorff(T)",
		},
		Conclusion: "t1_space(T)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], hausdorffT Fact) {
			// T1 unfolded on the goal: two distinct points of the space,
			// and an open set about the first missing the second.
			a.Do(Unfold(T1SpaceDef))
			a.Fix("x")
			a.Fix("y")
			distinct := a.Assume()
			u, _, separated := a.Obtain2(
				"the Hausdorff property puts x and y in disjoint open sets u and v",
				"∃u v:set(A). u ∈ T ∧ v ∈ T ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅",
				By(hausdorffT, distinct, topological_space.HausdorffDef))
			a.Take(u)
			a.Show(
				"u is open and holds x, and misses y, which lies in v disjoint from u",
				BySets(separated))
		}),
})}

// T1ImpT0 — a T1 space is T0: the open neighbourhood of one of two
// distinct points missing the other holds exactly one of the two. No
// axiom enters, so the family is spelled.
var T1ImpT0 = t1ImpT0Thm{family.Add(registry.ProofEntry{
	Name: "T1ImpT0",
	Key:  "prop_c804ebc2743e8235",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)).",
		Hypotheses: []string{
			"t1_space(T)",
		},
		Conclusion: "t0_space(T)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], t1 Fact) {
			// T0 unfolded on the goal: two distinct points of the space,
			// and an open set holding exactly one of them.
			a.Do(Unfold(T0SpaceDef))
			a.Fix("x")
			a.Fix("y")
			distinct := a.Assume()
			u, missesY := a.Obtain(
				"T1 gives an open neighbourhood u of x missing y",
				"∃u:set(A). u ∈ T ∧ x ∈ u ∧ y ∉ u",
				By(t1, distinct, T1SpaceDef))
			a.Take(u)
			a.Show(
				"u is open and holds x but not y",
				By(missesY))
		}),
})}

// T1IffSingletonsClosed — a space is T1 exactly when its points are
// closed. Forward, the complement of a point x in the space is open by
// the pointwise criterion: each of its points has an open neighbourhood
// missing x, which lies in the space and so in the complement. Backward,
// for distinct x and y the complement of {y} in the space is an open
// neighbourhood of x missing y.
var T1IffSingletonsClosed = t1IffSingletonsClosedThm{family.Add(registry.ProofEntry{
	Name: "T1IffSingletonsClosed",
	Key:  "prop_2fee6b82d0d4d712",
	Build: topological_space.IsTopology.Law("t1_space(T) ⇔ ∀x:A. x ∈ ⋃T ⇒ closed_in({x})",
		func(a *Argument, T *Expr[Set[Set[A]]], topology topological_space.IsTopologyFact[on.T]) {
			a.Iff()

			a.Forward(
				"in a T1 space the complement of a point is open, each of "+
					"its points having an open neighbourhood missing the point",
				func(b *Argument, t1 Fact) {
					b.Fix("x")
					xIn := b.Assume()
					pointwise := b.Have(
						"each point y of the space other than x has an open neighbourhood inside the complement of {x}",
						"∀y:A. y ∈ ⋃T ∖ {x} ⇒ ∃v:set(A). v ∈ T ∧ v ⊆ ⋃T ∖ {x} ∧ y ∈ v",
						Derive(func(c *Argument) {
							c.Fix("y")
							yIn := c.Assume()
							yOther := c.Have(
								"y lies in the space and is not x",
								"y ∈ ⋃T ∧ y ≠ x",
								BySets(yIn))
							u, missesX := c.Obtain(
								"T1 gives an open neighbourhood u of y missing x",
								"∃u:set(A). u ∈ T ∧ y ∈ u ∧ x ∉ u",
								By(t1, xIn, yOther, T1SpaceDef))
							c.Take(u)
							c.Show(
								"u is open and holds y, and it lies in the space, the union of the open sets, without x",
								BySets(missesX))
						}))
					complementOpen := b.Have(
						"so the complement of {x} in the space is open, by the pointwise criterion",
						"⋃T ∖ {x} ∈ T",
						By(topology, pointwise, topological_space.OpenPointwise))
					b.Show(
						"{x} lies in the space, as x does, and its complement there is open: {x} is closed",
						By(xIn, complementOpen, set_order.SingSubset, topological_space.ClosedInDef))
				})

			a.Backward(
				"when points are closed, the complement of one of two distinct "+
					"points is an open neighbourhood of the other missing it",
				func(b *Argument, pointsClosed Fact) {
					// T1 unfolded on the goal: two distinct points of the
					// space, and an open set about the first missing the
					// second.
					b.Do(Unfold(T1SpaceDef))
					b.Fix("x")
					b.Fix("y")
					distinct := b.Assume()
					complementOpen := b.Have(
						"{y} is closed, so its complement in the space is open",
						"⋃T ∖ {y} ∈ T",
						By(pointsClosed, distinct, topological_space.ClosedInDef))
					b.Take(b.TermAs[Set[A]]("⋃T ∖ {y}"))
					b.Show(
						"⋃T ∖ {y} is open, holds x, a point of the space other than y, and misses y",
						BySets(complementOpen, distinct))
				})
		}),
})}

// T1FiniteClosed — in a T1 space every finite set of points is closed.
// By induction on the set: the empty set is closed, and a set enlarged by
// one point x of the space is the union of the closed singleton {x} with
// the set before, closed by the induction hypothesis.
var T1FiniteClosed = t1FiniteClosedThm{family.Add(registry.ProofEntry{
	Name: "T1FiniteClosed",
	Key:  "prop_6f33fbc975ab59c9",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"t1_space(T)",
			"finite(s)",
			"s ⊆ ⋃T",
		},
		Conclusion: "closed_in(s)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology topological_space.IsTopologyFact[on.T],
			s *Expr[Set[A]],
			t1, finiteS, inside Fact,
		) {
			a.Show(
				"the induction carries the property to s, which is finite and lies in the space",
				ByInduction(finite_set.FiniteInduct, finiteS, Generalizing(inside),
					Case(
						"the empty set is closed",
						By(topology, topological_space.EmptyClosed)),
					Case(
						"one more point x of the space joins t as the union "+
							"with {x}, which is closed since the space is T1",
						Derive(func(b *Argument) {
							b.Fix("x")
							b.Fix("t")
							tClosedIfInside := b.Assume() // the induction hypothesis at t
							enlargedInside := b.Assume()
							within := b.Have(
								"so x and t lie in the space",
								"x ∈ ⋃T ∧ t ⊆ ⋃T",
								By(enlargedInside, set_order.InsertSubset))
							pointClosed := b.Have(
								"the space is T1, so the point x is closed",
								"closed_in({x})",
								By(topology, t1, within, T1IffSingletonsClosed))
							asUnion := b.Have(
								"one more point is the union with its singleton",
								"insert(x, t) = {x} ∪ t",
								BySets())
							b.Do(asUnion.Rw())
							b.Show(
								"{x} is closed, t is closed by the induction hypothesis, and two closed sets unite to a closed set",
								By(topology, pointClosed, tClosedIfInside, within, topological_space.UnionClosed))
						}))))
		}),
})}

// T1Subtopology — a subspace of a T1 space is T1: two distinct points of
// the subspace are points of the space, and the trace on s of an open
// neighbourhood of one missing the other is open in the subspace and
// still misses the other. No axiom enters, so the family is spelled.
var T1Subtopology = t1SubtopologyThm{family.Add(registry.ProofEntry{
	Name: "T1Subtopology",
	Key:  "prop_8ccc9de5cc46cefd",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s:set(A).",
		Hypotheses: []string{
			"t1_space(T)",
		},
		Conclusion: "t1_space(subtopology(T, s))",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], s *Expr[Set[A]], t1 Fact) {
			// T1 unfolded on the goal and on the hypothesis: of two distinct
			// points, an open set about the first missing the second — of the
			// subspace in the goal, of the space in the hypothesis.
			a.Do(Unfold(T1SpaceDef))
			a.Fix("x")
			a.Fix("y")
			distinct := a.Assume()
			inSpace := a.Have(
				"the points of the subspace are the points of the space in s",
				"x ∈ ⋃T ∩ s ∧ y ∈ ⋃T ∩ s",
				BySets(distinct, topological_space.SubtopologySpace.At(T, s)))
			u, missesY := a.ObtainAs[Set[A]](
				"so x and y are distinct points of the space, and T1 there gives an open u about x missing y",
				"∃u:set(A). u ∈ T ∧ x ∈ u ∧ y ∉ u",
				BySets(t1, inSpace, distinct))
			a.Take(a.TermAs[Set[A]]("u ∩ s"))
			a.Show(
				"the trace u ∩ s is open in the subspace, holds x, which lies in s, and misses y",
				BySets(inSpace, missesY, topological_space.TraceOpen.At(T, s, u)))
		}),
})}

// ---------------------------------------------------------------------------
// Regular spaces
// ---------------------------------------------------------------------------

// RegularIffClosedNeighbourhoods — a space is regular exactly when
// every open neighbourhood of a point holds an open one whose closure
// is inside it. Forward, regularity separates the point from the closed
// complement of the neighbourhood w by disjoint open u and v; the
// complement of v is closed and holds u, so it holds the closure of u,
// and it lies in w. Backward, a point outside a closed set c has such a
// u inside the open complement of c, and the complement of the closure
// of u is an open set around c disjoint from u.
var RegularIffClosedNeighbourhoods = regularIffClosedNeighbourhoodsThm{family.Add(registry.ProofEntry{
	Name: "RegularIffClosedNeighbourhoods",
	Key:  "prop_9fa30f12dfd2e10c",
	Build: topological_space.IsTopology.Law("regular_space(T) ⇔ "+
		"∀w:set(A). ∀x:A. w ∈ T ∧ x ∈ w ⇒ ∃u:set(A). u ∈ T ∧ x ∈ u ∧ closure(u) ⊆ w",
		func(a *Argument, T *Expr[Set[Set[A]]], topology topological_space.IsTopologyFact[on.T]) {
			a.Iff()

			a.Forward(
				"regularity separates x from the closed complement of w, "+
					"and the closure of the open set about x misses the other",
				func(b *Argument, regular Fact) {
					b.Fix("w")
					b.Fix("x")
					given := b.Conjuncts(
						b.Assume(),
						"w is open",
						"x lies in w")
					wOpen, xInW := given[0], given[1]
					complementClosed := b.Have(
						"the complement of the open set w in the space is closed",
						"closed_in(⋃T ∖ w)",
						By(wOpen, topological_space.OpenClosedComplement))
					outside := b.Have(
						"x is a point of the space outside that complement",
						"x ∈ ⋃T ∧ x ∉ ⋃T ∖ w",
						BySets(wOpen, xInW))
					u, _, separated := b.Obtain2(
						"regularity gives disjoint open sets u about x and v around the complement of w",
						"∃u v:set(A). u ∈ T ∧ v ∈ T ∧ x ∈ u ∧ ⋃T ∖ w ⊆ v ∧ u ∩ v = ∅",
						By(regular, complementClosed, outside, RegularSpaceDef))
					uOutsideV := b.Have(
						"u lies in the space outside v",
						"u ⊆ ⋃T ∖ v",
						BySets(separated))
					closureOutsideV := b.Have(
						"the complement of the open set v is closed and holds u, so it holds the closure of u",
						"closure(u) ⊆ ⋃T ∖ v",
						By(uOutsideV, separated, topological_space.OpenClosedComplement, topological_space.ClosureMinimal))
					b.Take(u)
					b.Show(
						"u is open and holds x, and its closure misses v, which holds every point of the space outside w",
						BySets(closureOutsideV, separated))
				})

			a.Backward(
				"a point outside a closed set c has an open neighbourhood whose "+
					"closure misses c, and the complement of that closure surrounds c",
				func(b *Argument, shrinking Fact) {
					// Regularity unfolded on the goal: a closed set, a point of
					// the space outside it, and disjoint open sets about each.
					b.Do(Unfold(RegularSpaceDef))
					b.Fix("c")
					x := b.FixAs[A]("x")
					given := b.Conjuncts(
						b.Assume(),
						"c is closed",
						"x lies in the space",
						"x is not in c")
					cClosed, xIn, xOut := given[0], given[1], given[2]
					complementOpen := b.Have(
						"the complement of the closed set c in the space is open",
						"⋃T ∖ c ∈ T",
						By(cClosed, topological_space.ClosedInDef))
					u, shrunk := b.ObtainAs[Set[A]](
						"it holds x, so it holds an open u about x whose closure is still inside it",
						"∃u:set(A). u ∈ T ∧ x ∈ u ∧ closure(u) ⊆ ⋃T ∖ c",
						BySets(shrinking.At(b.TermAs[Set[A]]("⋃T ∖ c"), x), complementOpen, xIn, xOut))
					closureClosed := b.Have(
						"the closure of u is closed, u lying in the space",
						"closed_in(closure(u))",
						By(topology, shrunk, set_order.MemberSubsetUnions, topological_space.ClosureClosed))
					around := b.Have(
						"so c lies in the space, and the complement there of the closure of u is open",
						"c ⊆ ⋃T ∧ ⋃T ∖ closure(u) ∈ T",
						By(closureClosed, cClosed, topological_space.ClosedInDef))
					b.Take(u)
					b.Take(b.TermAs[Set[A]]("⋃T ∖ closure(u)"))
					b.Show(
						"u and the complement of its closure are open and "+
							"disjoint, u holds x, and c misses the closure of u",
						BySets(around, shrunk, topological_space.SubsetClosure.At(T, u)))
				})
		}),
})}

// RegularSubtopology — a subspace of a regular space is regular. A
// closed set of the subspace is the trace d ∩ s of a closed set d of the
// space, and a point of the subspace outside the trace is a point of the
// space outside d; the traces of the disjoint open sets about the point
// and around d are open in the subspace and disjoint. No axiom enters,
// so the family is spelled.
var RegularSubtopology = regularSubtopologyThm{family.Add(registry.ProofEntry{
	Name: "RegularSubtopology",
	Key:  "prop_81b1d618731f5bb1",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s:set(A).",
		Hypotheses: []string{
			"regular_space(T)",
		},
		Conclusion: "regular_space(subtopology(T, s))",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], s *Expr[Set[A]], regular Fact) {
			// Regularity unfolded on the goal and on the hypothesis: a closed
			// set, a point outside it, and disjoint open sets about each — of
			// the subspace in the goal, of the space in the hypothesis.
			a.Do(Unfold(RegularSpaceDef))
			a.Fix("c")
			a.Fix("x")
			given := a.Conjuncts(
				a.Assume(),
				"c is closed in the subspace",
				"x is a point of the subspace",
				"x is not in c")
			cClosed, xIn, xOut := given[0], given[1], given[2]
			_, trace := a.Obtain(
				"a closed set of the subspace is the trace d ∩ s of a closed set d of the space",
				"∃d:set(A). closed_in(T, d) ∧ c = d ∩ s",
				By(cClosed, topological_space.ClosedInSubtopology))
			outsideD := a.Have(
				"x is a point of the space in s, and outside d, as it is outside the trace of d",
				"x ∈ ⋃T ∧ x ∈ s ∧ x ∉ d",
				BySets(trace, xIn, xOut, topological_space.SubtopologySpace.At(T, s)))
			u, v, separated := a.Obtain2As[Set[A], Set[A]](
				"regularity separates x from d by disjoint open sets u and v",
				"∃u v:set(A). u ∈ T ∧ v ∈ T ∧ x ∈ u ∧ d ⊆ v ∧ u ∩ v = ∅",
				By(regular, trace, outsideD))
			a.Take(a.TermAs[Set[A]]("u ∩ s"))
			a.Take(a.TermAs[Set[A]]("v ∩ s"))
			a.Show(
				"the traces of u and v are open in the subspace and "+
					"disjoint, u ∩ s holds x, and v ∩ s holds c = d ∩ s",
				BySets(
					trace,
					outsideD,
					separated,
					topological_space.TraceOpen.At(T, s, u),
					topological_space.TraceOpen.At(T, s, v)))
		}),
})}

// RegularT0ImpHausdorff — a regular T0 space is Hausdorff. Of two
// distinct points some open w holds exactly one; the complement of w in
// the space is closed, so regularity separates each point of w from it,
// and so from each point of the space outside w. Whichever of the two
// points w holds, the separating open sets are the ones asked for. No
// axiom enters, so the family is spelled.
var RegularT0ImpHausdorff = regularT0ImpHausdorffThm{family.Add(registry.ProofEntry{
	Name: "RegularT0ImpHausdorff",
	Key:  "prop_591c228a8c05b2fb",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)).",
		Hypotheses: []string{
			"regular_space(T)",
			"t0_space(T)",
		},
		Conclusion: "hausdorff(T)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], regular, t0 Fact) {
			// Hausdorff unfolded on the goal: two distinct points of the
			// space, and disjoint open sets about each.
			a.Do(Unfold(topological_space.HausdorffDef))
			x := a.FixAs[A]("x")
			y := a.FixAs[A]("y")
			distinct := a.Assume()
			_, tells := a.Obtain(
				"T0 gives an open set w holding exactly one of x and y",
				"∃w:set(A). w ∈ T ∧ ¬(x ∈ w ⇔ y ∈ w)",
				By(t0, distinct, T0SpaceDef))
			complementClosed := a.Have(
				"the complement of the open set w in the space is closed",
				"closed_in(T, ⋃T ∖ w)",
				By(tells, topological_space.OpenClosedComplement))
			separates := a.Have(
				"regularity separates each point of w from each point of the space outside w",
				"∀p q:A. p ∈ w ∧ q ∈ ⋃T ∧ q ∉ w ⇒ ∃u v:set(A). u ∈ T ∧ v ∈ T ∧ p ∈ u ∧ q ∈ v ∧ u ∩ v = ∅",
				Derive(func(b *Argument) {
					b.Fix("p")
					b.Fix("q")
					given := b.Assume()
					pOutside := b.Have(
						"p is a point of the space outside the complement of w",
						"p ∈ ⋃T ∧ p ∉ ⋃T ∖ w",
						BySets(tells, given))
					aroundComplement := b.Have(
						"so regularity puts p and the complement of w in disjoint open sets",
						"∃u v:set(A). u ∈ T ∧ v ∈ T ∧ p ∈ u ∧ ⋃T ∖ w ⊆ v ∧ u ∩ v = ∅",
						By(regular, complementClosed, pOutside, RegularSpaceDef))
					b.Show(
						"and q lies in that complement",
						BySets(aroundComplement, given))
				}))

			a.Cases(a.Term("x ∈ w"))
			a.When(
				"w holds x and so not y: x is separated from y",
				func(b *Argument, xIn Fact) {
					b.Show(
						"the open sets separating x in w from y outside it",
						By(separates.At(x, y), xIn, tells, distinct))
				})
			a.Otherwise(
				"w holds y and not x: y is separated from x, and the two open sets change places",
				func(b *Argument, xOut Fact) {
					u, v, swapped := b.Obtain2(
						"open sets u about y in w and v about x outside it, disjoint",
						"∃u v:set(A). u ∈ T ∧ v ∈ T ∧ y ∈ u ∧ x ∈ v ∧ u ∩ v = ∅",
						By(separates.At(y, x), xOut, tells, distinct))
					b.Take(v)
					b.Take(u)
					b.Show(
						"v about x and u about y are open and disjoint",
						By(swapped, set_algebra.InterComm))
				})
		}),
})}

// CompactHausdorffRegular — a compact Hausdorff space is regular: a
// closed set is a closed part of the compact space, so compact, and a
// point outside a compact set of a Hausdorff space is separated from it.
var CompactHausdorffRegular = compactHausdorffRegularThm{family.Add(registry.ProofEntry{
	Name: "CompactHausdorffRegular",
	Key:  "prop_a690ec2d6c46ec84",
	Build: topological_space.IsTopology.Law(Statement{
		Hypotheses: []string{
			"hausdorff(T)",
			"compact_in(⋃T)",
		},
		Conclusion: "regular_space(T)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology topological_space.IsTopologyFact[on.T],
			hausdorffT, compactSpace Fact,
		) {
			// Regularity unfolded on the goal: a closed set, a point of the
			// space outside it, and disjoint open sets about each.
			a.Do(Unfold(RegularSpaceDef))
			a.Fix("c")
			a.Fix("x")
			given := a.Conjuncts(
				a.Assume(),
				"c is closed",
				"x lies in the space",
				"x is not in c")
			cClosed, xIn, xOut := given[0], given[1], given[2]
			compactC := a.Have(
				"c is closed, so it lies in the compact space and is compact",
				"compact_in(c)",
				By(compactSpace, cClosed, compact.ClosedSubsetCompact, topological_space.ClosedInDef))
			a.Show(
				"a point outside a compact set of a Hausdorff space is separated from it",
				By(hausdorffT, topology, compactC, xIn, xOut, compact.PointCompactSeparation))
		}),
})}
