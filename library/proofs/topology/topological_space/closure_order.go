// closure_order.go — closure operators and complete lattices of closed and open sets.

package topological_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/registry"
)

// ClosureOperator — topological closure is a closure operator on the subsets
// of the space: it selects the least closed set containing each subset.
var ClosureOperator = closureOperatorThm{family.Add(registry.ProofEntry{
	Name: "ClosureOperator",
	Key:  "prop_c97edfaec348c81e",
	Build: IsTopology.Law("closure_operator_on({s:set(A) | s ⊆ ⋃T}, "+
		"    λs:set(A). λt:set(A). s ⊆ t, "+
		"    λs:set(A). closure(s))",
		func(a *Argument, topology IsTopologyFact[on.T]) {
			T := a.TermAs[Set[Set[A]]]("T")
			space := a.TermAs[Set[A]]("⋃T")
			closedSets := a.TermAs[Set[Set[A]]]("{s:set(A) | closed_in(s)}")
			powerset := a.Simplified(order.PowersetCompleteLattice.At(space))
			within := a.Have(
				"closed sets lie inside the space",
				"{s:set(A) | closed_in(s)} ⊆ {s:set(A) | s ⊆ ⋃T}",
				BySets(ClosedInDef))
			least := a.Have(
				"closure is the least closed set containing each subset of the space",
				Statement{
					Binders: "∀s:set(A).",
					Hypotheses: []string{
						"s ∈ {t:set(A) | t ⊆ ⋃T}",
					},
					Conclusion: "closure(s) ∈ {t:set(A) | closed_in(t)} ∧ " +
						"s ⊆ closure(s) ∧ " +
						"(∀t:set(A). t ∈ {u:set(A) | closed_in(u)} ∧ s ⊆ t ⇒ closure(s) ⊆ t)",
				},
				BySets(ClosureClosed.Read(topology), SubsetClosure.Inst[A]().At(T), ClosureMinimal.Inst[A]().At(T)))
			a.Show(
				"least closed supersets give a closure operator",
				By(
					order.CompleteLatticeOnPartialOrder.Read(powerset),
					least,
					within,
					Where(order.ClosureFromLeast, "F", closedSets)))
		}),
})}

// ClosedSetsCompleteLattice — the closed subsets form a complete lattice under
// inclusion. Suprema are closures of unions; infima are intersections within
// the space, so the empty family's infimum is the space itself.
var ClosedSetsCompleteLattice = closedSetsCompleteLatticeThm{family.Add(registry.ProofEntry{
	Name: "ClosedSetsCompleteLattice",
	Key:  "prop_616adc2f95b7ad15",
	Build: IsTopology.Law("complete_lattice_on({s:set(A) | closed_in(s)}, "+
		"    λs:set(A). λt:set(A). s ⊆ t, "+
		"    λF:set(set(A)). closure(⋃F), "+
		"    λF:set(set(A)). ⋃T ∩ ⋂F)",
		func(a *Argument, topology IsTopologyFact[on.T]) {
			space := a.TermAs[Set[A]]("⋃T")
			inclusion := a.TermAs[Fun2[Set[A], Set[A], Bool]]("λs:set(A). λt:set(A). s ⊆ t")
			unions := a.TermAs[Fun[Set[Set[A]], Set[A]]]("λF:set(set(A)). ⋃F")
			intersections := a.TermAs[Fun[Set[Set[A]], Set[A]]]("λF:set(set(A)). ⋃T ∩ ⋂F")
			carrier := a.TermAs[Set[Set[A]]]("{s:set(A) | s ⊆ ⋃T}")
			close := a.TermAs[Fun[Set[A], Set[A]]]("λs:set(A). closure(s)")
			powerset := a.Simplified(order.PowersetCompleteLattice.At(space))
			closure := a.Simplified(ClosureOperator.Read(topology))
			fixed := a.Have(
				"the closure fixed points inherit the powerset's complete lattice",
				"complete_lattice_on({s:set(A) | s ⊆ ⋃T ∧ closure(s) = s}, "+
					"    λs:set(A). λt:set(A). s ⊆ t, "+
					"    λF:set(set(A)). closure(⋃F), "+
					"    λF:set(set(A)). ⋃T ∩ ⋂F)",
				By(
					closure,
					powerset,
					order.ClosureFixedPointsCompleteLattice.At(inclusion, unions, intersections, carrier, close)))
			closed := a.Have(
				"the fixed points in the space are exactly its closed subsets",
				"{s:set(A) | closed_in(s)} = {s:set(A) | s ⊆ ⋃T ∧ closure(s) = s}",
				BySets(ClosedIffClosure.Read(topology)))
			a.Show(
				"the fixed-point lattice is therefore the lattice of closed subsets",
				closed.Rw(),
				By(fixed))
		}),
})}

// InteriorOperator — interior is a closure operator for reverse inclusion on
// the subsets of the space: it selects the greatest open subset of each set.
var InteriorOperator = interiorOperatorThm{family.Add(registry.ProofEntry{
	Name: "InteriorOperator",
	Key:  "prop_ef490834a84463b2",
	Build: IsTopology.Law("closure_operator_on({s:set(A) | s ⊆ ⋃T}, "+
		"    λs:set(A). λt:set(A). t ⊆ s, "+
		"    λs:set(A). interior(s))",
		func(a *Argument, topology IsTopologyFact[on.T]) {
			T := a.TermAs[Set[Set[A]]]("T")
			space := a.TermAs[Set[A]]("⋃T")
			powerset := a.Simplified(order.PowersetCompleteLattice.At(space))
			reversed := a.Simplified(order.CompleteLatticeOnDual.Read(powerset))
			within := a.Have(
				"open sets lie inside the space",
				"T ⊆ {s:set(A) | s ⊆ ⋃T}",
				BySets())
			greatest := a.Have(
				"interior is the greatest open subset of each subset of the space",
				Statement{
					Binders: "∀s:set(A).",
					Hypotheses: []string{
						"s ∈ {t:set(A) | t ⊆ ⋃T}",
					},
					Conclusion: "interior(s) ∈ T ∧ interior(s) ⊆ s ∧ (∀t:set(A). t ∈ T ∧ t ⊆ s ⇒ t ⊆ interior(s))",
				},
				BySets(
					InteriorOpen.Read(topology),
					InteriorSubset.Inst[A]().At(T),
					InteriorMaximal.Inst[A]().At(T)))
			a.Show(
				"greatest open subsets give a closure operator for reverse inclusion",
				By(
					order.CompleteLatticeOnPartialOrder.Read(reversed),
					greatest,
					within,
					Where(order.ClosureFromLeast, "F", T)))
		}),
})}

// OpenSetsCompleteLattice — the open subsets form a complete lattice under
// inclusion. Suprema are unions; infima are interiors of intersections within
// the space, so the empty family's infimum is the space itself.
var OpenSetsCompleteLattice = openSetsCompleteLatticeThm{family.Add(registry.ProofEntry{
	Name: "OpenSetsCompleteLattice",
	Key:  "prop_a5334c5356cd5cbe",
	Build: IsTopology.Law("complete_lattice_on(T, "+
		"    λs:set(A). λt:set(A). s ⊆ t, "+
		"    λF:set(set(A)). ⋃F, "+
		"    λF:set(set(A)). interior(⋃T ∩ ⋂F))",
		func(a *Argument, topology IsTopologyFact[on.T]) {
			space := a.TermAs[Set[A]]("⋃T")
			reverseInclusion := a.TermAs[Fun2[Set[A], Set[A], Bool]]("λs:set(A). λt:set(A). t ⊆ s")
			intersections := a.TermAs[Fun[Set[Set[A]], Set[A]]]("λF:set(set(A)). ⋃T ∩ ⋂F")
			unions := a.TermAs[Fun[Set[Set[A]], Set[A]]]("λF:set(set(A)). ⋃F")
			carrier := a.TermAs[Set[Set[A]]]("{s:set(A) | s ⊆ ⋃T}")
			interior := a.TermAs[Fun[Set[A], Set[A]]]("λs:set(A). interior(s)")
			powerset := a.Simplified(order.PowersetCompleteLattice.At(space))
			reversed := a.Simplified(order.CompleteLatticeOnDual.Read(powerset))
			operator := a.Have(
				"interior is a closure operator for reverse inclusion",
				"closure_operator_on({s:set(A) | s ⊆ ⋃T}, λs:set(A). λt:set(A). t ⊆ s, λs:set(A). interior(s))",
				By(InteriorOperator.Read(topology)))
			fixed := a.Have(
				"the interior fixed points inherit a complete lattice for reverse inclusion",
				"complete_lattice_on({s:set(A) | s ⊆ ⋃T ∧ interior(s) = s}, "+
					"    λs:set(A). λt:set(A). t ⊆ s, "+
					"    λF:set(set(A)). interior(⋃T ∩ ⋂F), "+
					"    λF:set(set(A)). ⋃F)",
				By(
					operator,
					reversed,
					order.ClosureFixedPointsCompleteLattice.At(
						reverseInclusion, intersections, unions, carrier, interior)))
			open := a.Have(
				"the fixed points in the space are exactly its open subsets",
				"T = {s:set(A) | s ⊆ ⋃T ∧ interior(s) = s}",
				Simp(Rev(OpenIffInterior.Read(topology))),
				BySets())
			openLattice := a.Simplified(fixed, Rev(open))
			a.Show(
				"duality gives the complete lattice of open subsets under inclusion",
				By(order.CompleteLatticeOnDual.Read(openLattice)))
		}),
})}
