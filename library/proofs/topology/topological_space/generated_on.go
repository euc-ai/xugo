// generated_on.go — generation among topologies on a fixed space.

package topological_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// TopologyGeneratedOnDef — generation on X adjoins X to the generating family.
var TopologyGeneratedOnDef = topologyGeneratedOnDefThm{family.Define(registry.DefEntry{
	Name:  "TopologyGeneratedOnDef",
	Key:   "prop_4afff79220acfd5d",
	Const: "topology_generated_on",
	Type:  "set(A) → set(set(A)) → set(set(A))",
	Equations: []string{
		"∀X:set(A). ∀b:set(set(A)). topology_generated_on(X, b) = topology_generated(b ∪ {X})",
	},
	Deps: []registry.EntryLike{TopologyGeneratedDef},
})}

// GeneratedOnTopology — adjoining the carrier and generating gives a topology.
var GeneratedOnTopology = generatedOnTopologyThm{family.Add(registry.ProofEntry{
	Name: "GeneratedOnTopology",
	Key:  "prop_1be69d3b38e025d0",
	Build: family.Theorem("∀X:set(A). ∀b:set(set(A)). is_topology(topology_generated_on(X, b))",
		func(a *Argument, X *Expr[Set[A]], b *Expr[Set[Set[A]]]) {
			a.Show(
				"generation gives a topology",
				Unfold(TopologyGeneratedOnDef),
				By(GeneratedTopology))
		}),
})}

// GeneratedOnSpace — generators contained in X generate exactly the space X.
var GeneratedOnSpace = generatedOnSpaceThm{family.Add(registry.ProofEntry{
	Name: "GeneratedOnSpace",
	Key:  "prop_25167c552c1b3bb8",
	Build: family.Theorem(Statement{
		Binders: "∀X:set(A). ∀b:set(set(A)).",
		Hypotheses: []string{
			"b ⊆ {s:set(A) | s ⊆ X}",
		},
		Conclusion: "⋃topology_generated_on(X, b) = X",
	},
		func(a *Argument, X *Expr[Set[A]], b *Expr[Set[Set[A]]], within Fact) {
			a.Show(
				"adjoining X makes the union of the generators equal to X",
				Unfold(TopologyGeneratedOnDef),
				Simp(Fwd(GeneratedSpace)),
				BySets(within))
		}),
})}

// GeneratedOnContains — generation on a carrier contains each generator.
var GeneratedOnContains = generatedOnContainsThm{family.Add(registry.ProofEntry{
	Name: "GeneratedOnContains",
	Key:  "prop_aaa522cfe9c6cdb",
	Build: family.Theorem("∀X:set(A). ∀b:set(set(A)). b ⊆ topology_generated_on(X, b)",
		func(a *Argument, X *Expr[Set[A]], b *Expr[Set[Set[A]]]) {
			a.Show(
				"the original generators are among the enlarged generating family",
				Unfold(TopologyGeneratedOnDef),
				BySets(GeneratedContains))
		}),
})}

// GeneratedOnMinimal — every topology on X containing the generators contains their generated topology.
var GeneratedOnMinimal = generatedOnMinimalThm{family.Add(registry.ProofEntry{
	Name: "GeneratedOnMinimal",
	Key:  "prop_8ed25684827e3a6f",
	Build: family.Theorem(Statement{
		Binders: "∀X:set(A). ∀T b:set(set(A)).",
		Hypotheses: []string{
			"is_topology(T)",
			"⋃T = X",
			"b ⊆ T",
		},
		Conclusion: "topology_generated_on(X, b) ⊆ T",
	},
		func(a *Argument, X *Expr[Set[A]], T, b *Expr[Set[Set[A]]], assumptions Fact) {
			parts := a.Conjuncts(
				assumptions,
				"the containing family is a topology",
				"its carrier is X",
				"it contains the generators")
			topology, space, contains := parts[0], parts[1], parts[2]
			a.Do(Unfold(TopologyGeneratedOnDef))
			carrierOpen := a.Have(
				"the carrier itself is open",
				"X ∈ T",
				By(Normalized, SpaceOpen.Read(topology), space))
			augmented := a.Have(
				"the topology contains all the enlarged generators",
				"b ∪ {X} ⊆ T",
				By(
					carrierOpen,
					contains,
					set_order.SingSubset.Inst[Set[A]](),
					set_order.UnionSubset.Inst[Set[A]]()))
			a.Show(
				"minimality applies to the enlarged family",
				By(GeneratedMinimal.Read(topology), augmented))
		}),
})}

// GeneratedOnClosureOperator — generation is a closure operator on the families of subsets of X:
// it selects the least topology on X containing each family.
var GeneratedOnClosureOperator = generatedOnClosureOperatorThm{family.Add(registry.ProofEntry{
	Name: "GeneratedOnClosureOperator",
	Key:  "prop_71ee2584a25e022",
	Build: family.Theorem("∀X:set(A). "+
		"    closure_operator_on({b:set(set(A)) | b ⊆ {s:set(A) | s ⊆ X}}, "+
		"        λb:set(set(A)). λd:set(set(A)). b ⊆ d, "+
		"        λb:set(set(A)). topology_generated_on(X, b))",
		func(a *Argument, X *Expr[Set[A]]) {
			subsets := a.TermAs[Set[Set[A]]]("{s:set(A) | s ⊆ X}")
			topologies := a.TermAs[Set[Set[Set[A]]]]("{T:set(set(A)) | is_topology(T) ∧ ⋃T = X}")
			powerset := a.Simplified(order.PowersetCompleteLattice.At(subsets))
			within := a.Have(
				"each topology on X is a family of subsets of X",
				"{T:set(set(A)) | is_topology(T) ∧ ⋃T = X} ⊆ {b:set(set(A)) | b ⊆ {s:set(A) | s ⊆ X}}",
				BySets())
			least := a.Have(
				"generation selects the least topology on X containing its generators",
				Statement{
					Binders: "∀b:set(set(A)).",
					Hypotheses: []string{
						"b ∈ {d:set(set(A)) | d ⊆ {s:set(A) | s ⊆ X}}",
					},
					Conclusion: "topology_generated_on(X, b) ∈ {T:set(set(A)) | is_topology(T) ∧ ⋃T = X} ∧ " +
						"b ⊆ topology_generated_on(X, b) ∧ " +
						"(∀T:set(set(A)). " +
						"    T ∈ {U:set(set(A)) | is_topology(U) ∧ ⋃U = X} ∧ b ⊆ T ⇒ topology_generated_on(X, b) ⊆ T)",
				},
				Derive(func(c *Argument) {
					b := c.FixAs[Set[Set[A]]]("b")
					generators := c.Assume()
					c.Show(
						"the generated topology contains the family and is least",
						SplitConj(
							Case(
								"the generated topology is on X and contains the generators",
								SplitConj(
									Case(
										"generation gives a topology whose space is X",
										BySets(generators, GeneratedOnTopology.At(X, b), GeneratedOnSpace.At(X, b))),
									Case(
										"each generator is open",
										By(GeneratedOnContains)),
								)),
							Case(
								"every topology on X containing the generators contains their generation",
								Derive(func(d *Argument) {
									T := d.FixAs[Set[Set[A]]]("T")
									containing := d.Assume()
									d.Show(
										"minimality places the generated topology inside T",
										BySets(containing, GeneratedOnMinimal.At(X, T, b)))
								})),
						))
				}))
			a.Show(
				"least topologies give a closure operator",
				By(
					order.CompleteLatticeOnPartialOrder.Read(powerset),
					least,
					within,
					Where(order.ClosureFromLeast, "F", topologies)))
		}),
})}
