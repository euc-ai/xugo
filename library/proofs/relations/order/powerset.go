// powerset.go — the subsets of a fixed set form a complete lattice.

package order

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// PowersetCompleteLattice — inclusion orders the subsets of X as a complete
// lattice: union gives suprema and intersection with X gives infima.
// The relative intersection gives X itself for the empty family's infimum.
var PowersetCompleteLattice = powersetCompleteLatticeThm{family.Add(registry.ProofEntry{
	Name: "PowersetCompleteLattice",
	Key:  "prop_cf61e18f60e21c6b",
	Build: family.Theorem("∀X:set(A). "+
		"    complete_lattice_on({s:set(A) | s ⊆ X}, "+
		"        λs:set(A). λt:set(A). s ⊆ t, "+
		"        λF:set(set(A)). ⋃F, "+
		"        λF:set(set(A)). X ∩ ⋂F)",
		func(a *Argument, X *Expr[Set[A]]) {
			a.Show(
				"inclusion, union, and relative intersection satisfy the carrier lattice axioms",
				Unfold(CompleteLatticeOn),
				SplitConjAll(
					Case(
						"inclusion is a partial order on the subsets of X",
						Unfold(PartialOrderOn),
						Unfold(PreorderOn),
						SplitConjAll(
							Case(
								"every set includes itself",
								By(set_order.SubsetRefl)),
							Case(
								"inclusions compose",
								By(set_order.SubsetTrans)),
							Case(
								"mutual inclusion gives equality",
								By(set_order.SubsetAntisym)),
						)),
					Case(
						"the union is a supremum within the powerset",
						Unfold(HasSupOnDef),
						Unfold(UpperBoundDef),
						Derive(func(b *Argument) {
							F := b.FixAs[Set[Set[A]]]("F")
							within := b.Assume()
							b.Show(
								"the union lies in X, contains each member, and is below every upper bound",
								SplitConjAll(
									Case(
										"the family is a subset of the powerset",
										By(within)),
									Case(
										"the union stays inside X",
										Derive(func(c *Argument) {
											members := c.Have(
												"every member of the family lies inside X",
												"∀t:set(A). t ∈ F ⇒ t ⊆ X",
												BySets(within))
											c.Show(
												"their union therefore lies inside X",
												By(members, set_order.UnionsSubset.At(F, X)))
										})),
									Case(
										"each member lies in the union",
										By(set_order.MemberSubsetUnions)),
									Case(
										"every upper bound contains the union",
										By(set_order.UnionsSubset)),
								))
						})),
					Case(
						"the relative intersection is an infimum within the powerset",
						Unfold(HasInfOnDef),
						Unfold(LowerBoundDef),
						BySets()),
				))
		}),
})}
