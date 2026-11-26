// normal.go — normal spaces: a compact Hausdorff space is normal, and in a
// normal space a closed set inside an open set has an open neighbourhood
// whose closure still lies in the open set.

package separation

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Normal spaces
// ---------------------------------------------------------------------------

// CompactHausdorffNormal — a compact Hausdorff space is normal. Two
// disjoint closed sets are closed parts of the compact space, so compact
// themselves, and two disjoint compact sets of a Hausdorff space lie in
// disjoint open sets.
var CompactHausdorffNormal = compactHausdorffNormalThm{family.Add(registry.ProofEntry{
	Name: "CompactHausdorffNormal",
	Key:  "prop_37d2846ef0f86ab1",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)).",
		Hypotheses: []string{
			"is_topology(T)",
			"hausdorff(T)",
			"compact_in(T, ⋃T)",
		},
		Conclusion: "normal_space(T)",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], _ Fact) {
			// Normality unfolded on the goal; the hypothesis splits into
			// its three clauses.
			a.Do(Unfold(NormalSpaceDef))
			topology := a.Hyp("is_topology(T)")
			hausdorffT := a.Hyp("hausdorff(T)")
			compactSpace := a.Hyp("compact_in(T, ⋃T)")
			a.Fix("s")
			a.Fix("t")
			closedDisjoint := a.Assume()
			bothCompact := a.Have(
				"s and t are closed, so they lie in the compact space and are compact",
				"compact_in(T, s) ∧ compact_in(T, t)",
				By(compactSpace, closedDisjoint, compact.ClosedSubsetCompact, topological_space.ClosedInDef))
			a.Show(
				"two disjoint compact sets of a Hausdorff space lie in disjoint open sets",
				By(topology, hausdorffT, bothCompact, closedDisjoint, compact.CompactSeparation))
		}),
})}

// NormalShrink — in a normal space a closed set inside an open set u has
// an open neighbourhood whose closure still lies in u. The closed set c
// and the complement of u in the space are disjoint closed sets, so
// normality puts them in disjoint open sets v and w; the complement of w
// is closed and holds v, so it holds the closure of v, and it lies in u.
// No axiom enters, so the family is spelled. The step Urysohn's
// construction repeats at every dyadic level.
var NormalShrink = normalShrinkThm{family.Add(registry.ProofEntry{
	Name: "NormalShrink",
	Key:  "prop_76db3b8ae63de203",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀c u:set(A).",
		Hypotheses: []string{
			"normal_space(T)",
			"closed_in(T, c)",
			"u ∈ T",
			"c ⊆ u",
		},
		Conclusion: "∃v:set(A). v ∈ T ∧ c ⊆ v ∧ closure(T, v) ⊆ u",
	},
		func(a *Argument, T *Expr[Set[Set[A]]], c, u *Expr[Set[A]], normal, cClosed, uOpen, cInside Fact) {
			complementClosed := a.Have(
				"the complement of the open set u in the space is closed",
				"closed_in(T, ⋃T ∖ u)",
				By(uOpen, topological_space.OpenClosedComplement))
			disjoint := a.Have(
				"and it misses c, which lies inside u",
				"c ∩ (⋃T ∖ u) = ∅",
				BySets(cInside))
			v, _, separated := a.Obtain2(
				"normality puts c and the complement of u in disjoint open sets v and w",
				"∃v w:set(A). v ∈ T ∧ w ∈ T ∧ c ⊆ v ∧ ⋃T ∖ u ⊆ w ∧ v ∩ w = ∅",
				By(normal, disjoint, cClosed, complementClosed, NormalSpaceDef))
			vOutsideW := a.Have(
				"v lies in the space outside w",
				"v ⊆ ⋃T ∖ w",
				BySets(separated))
			closureOutsideW := a.Have(
				"the complement of the open set w is closed and holds v, so it holds the closure of v",
				"closure(T, v) ⊆ ⋃T ∖ w",
				By(vOutsideW, separated, topological_space.OpenClosedComplement, topological_space.ClosureMinimal))
			a.Take(v)
			a.Show(
				"v is open around c, and its closure misses w, which holds every point of the space outside u",
				BySets(closureOutsideW, separated))
		}),
})}

// ---------------------------------------------------------------------------
// Normal spaces among the others
// ---------------------------------------------------------------------------

// NormalIffShrink — a space is normal exactly when every closed set
// inside an open set has an open neighbourhood whose closure is still
// inside. Forward is NormalShrink. Backward, for disjoint closed s and t
// the complement of t in the space is an open set around s; an open v
// around s whose closure stays inside that complement, and the
// complement of that closure, are disjoint open sets around s and t.
var NormalIffShrink = normalIffShrinkThm{family.Add(registry.ProofEntry{
	Name: "NormalIffShrink",
	Key:  "prop_185f08fed0f33e6d",
	Build: topological_space.IsTopology.Law("normal_space(T) ⇔ "+
		"∀c u:set(A). closed_in(c) ∧ u ∈ T ∧ c ⊆ u ⇒ ∃v:set(A). v ∈ T ∧ c ⊆ v ∧ closure(v) ⊆ u",
		func(a *Argument, T *Expr[Set[Set[A]]], topology topological_space.IsTopologyFact[on.T]) {
			a.Iff()

			a.Forward(
				"a normal space shrinks a closed set inside an open one",
				func(b *Argument, normal Fact) {
					b.Show(
						"the shrinking step of a normal space",
						By(normal, NormalShrink))
				})

			a.Backward(
				"for disjoint closed s and t, shrink s inside the "+
					"complement of t; the complement of the closure surrounds t",
				func(b *Argument, shrinking Fact) {
					// Normality unfolded on the goal: two disjoint closed sets,
					// and disjoint open sets around each.
					b.Do(Unfold(NormalSpaceDef))
					b.Fix("s")
					b.Fix("t")
					closedDisjoint := b.Assume()
					readings := b.Have(
						"the closed sets lie in the space, and the complement of t there is open",
						"s ⊆ ⋃T ∧ t ⊆ ⋃T ∧ ⋃T ∖ t ∈ T",
						By(closedDisjoint, topological_space.ClosedInDef))
					sInside := b.Have(
						"s, disjoint from t, lies in that complement",
						"s ⊆ ⋃T ∖ t",
						BySets(closedDisjoint, readings))
					v, shrunk := b.ObtainAs[Set[A]](
						"so s has an open neighbourhood v whose closure stays inside the complement of t",
						"∃v:set(A). v ∈ T ∧ s ⊆ v ∧ closure(v) ⊆ ⋃T ∖ t",
						By(shrinking, sInside, closedDisjoint, readings))
					closureClosed := b.Have(
						"the closure of v is closed, v lying in the space",
						"closed_in(closure(v))",
						By(topology, shrunk, set_order.MemberSubsetUnions, topological_space.ClosureClosed))
					complementOpen := b.Have(
						"so its complement in the space is open",
						"⋃T ∖ closure(v) ∈ T",
						By(closureClosed, topological_space.ClosedInDef))
					b.Take(v)
					b.Take(b.TermAs[Set[A]]("⋃T ∖ closure(v)"))
					b.Show(
						"v around s and the complement of its closure around t are open and disjoint",
						BySets(complementOpen, shrunk, readings, topological_space.SubsetClosure.At(T, v)))
				})
		}),
})}

// NormalT1ImpRegular — a normal T1 space is regular: a point of the
// space is a closed set, disjoint from a closed set not holding it, and
// normality separates the two.
var NormalT1ImpRegular = normalT1ImpRegularThm{family.Add(registry.ProofEntry{
	Name: "NormalT1ImpRegular",
	Key:  "prop_2992b1838455b549",
	Build: topological_space.IsTopology.Law(Statement{
		Hypotheses: []string{
			"normal_space(T)",
			"t1_space(T)",
		},
		Conclusion: "regular_space(T)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology topological_space.IsTopologyFact[on.T],
			normal, t1 Fact,
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
			pointClosed := a.Have(
				"the space is T1, so the point x is closed",
				"closed_in({x})",
				By(topology, t1, xIn, T1IffSingletonsClosed))
			disjoint := a.Have(
				"and {x} misses c",
				"{x} ∩ c = ∅",
				BySets(xOut))
			u, v, separated := a.Obtain2(
				"normality puts {x} and c in disjoint open sets u and v",
				"∃u v:set(A). u ∈ T ∧ v ∈ T ∧ {x} ⊆ u ∧ c ⊆ v ∧ u ∩ v = ∅",
				By(normal, disjoint, pointClosed, cClosed, NormalSpaceDef))
			a.Take(u)
			a.Take(v)
			a.Show(
				"u holds x, v holds c, and the two are open and disjoint",
				By(separated, set_order.SingSubset))
		}),
})}

// NormalT1ImpHausdorff — a normal T1 space is Hausdorff: it is regular,
// its points being closed, and T0, and a regular T0 space is Hausdorff.
var NormalT1ImpHausdorff = normalT1ImpHausdorffThm{family.Add(registry.ProofEntry{
	Name: "NormalT1ImpHausdorff",
	Key:  "prop_14281d95ab8e54e3",
	Build: topological_space.IsTopology.Law(Statement{
		Hypotheses: []string{
			"normal_space(T)",
			"t1_space(T)",
		},
		Conclusion: "hausdorff(T)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology topological_space.IsTopologyFact[on.T],
			normal, t1 Fact,
		) {
			a.Show(
				"a normal T1 space is regular, a T1 space is T0, and a regular T0 space is Hausdorff",
				By(topology, normal, t1, NormalT1ImpRegular, T1ImpT0, RegularT0ImpHausdorff))
		}),
})}

// NormalClosedSubtopology — a closed subspace of a normal space is
// normal: two disjoint closed sets of the closed subspace c are closed
// sets of the space inside c, normality of the space puts them in
// disjoint open sets, and the traces of those on c are open in the
// subspace, disjoint, and still hold them.
var NormalClosedSubtopology = normalClosedSubtopologyThm{family.Add(registry.ProofEntry{
	Name: "NormalClosedSubtopology",
	Key:  "prop_c4fd50188df97481",
	Build: topological_space.IsTopology.Law(Statement{
		Binders: "∀c:set(A).",
		Hypotheses: []string{
			"normal_space(T)",
			"closed_in(T, c)",
		},
		Conclusion: "normal_space(subtopology(T, c))",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology topological_space.IsTopologyFact[on.T],
			c *Expr[Set[A]],
			normal, cClosed Fact,
		) {
			// Normality unfolded on the goal and on the hypothesis: two
			// disjoint closed sets, and disjoint open sets around each — of
			// the subspace in the goal, of the space in the hypothesis.
			a.Do(Unfold(NormalSpaceDef))
			a.Fix("s")
			a.Fix("t")
			closedDisjoint := a.Assume()
			closedInSpace := a.Have(
				"the closed sets of the closed subspace are the closed sets of the space inside c",
				"closed_in(T, s) ∧ s ⊆ c ∧ closed_in(T, t) ∧ t ⊆ c",
				By(topology, cClosed, closedDisjoint, topological_space.ClosedInClosedSubtopology))
			u, v, separated := a.Obtain2As[Set[A], Set[A]](
				"normality of the space puts s and t in disjoint open sets u and v",
				"∃u v:set(A). u ∈ T ∧ v ∈ T ∧ s ⊆ u ∧ t ⊆ v ∧ u ∩ v = ∅",
				By(normal, closedDisjoint, closedInSpace))
			a.Take(a.TermAs[Set[A]]("u ∩ c"))
			a.Take(a.TermAs[Set[A]]("v ∩ c"))
			a.Show(
				"the traces of u and v on c are open in the subspace "+
					"and disjoint, and hold s and t, which lie in c",
				BySets(
					closedInSpace,
					separated,
					topological_space.TraceOpen.At(T, c, u),
					topological_space.TraceOpen.At(T, c, v)))
		}),
})}
