// topological_space.go — the structure and its axioms, the discrete
// topology and the intersection of topologies, and what the axioms say
// about open sets. The notions
// stated over one space — closed sets, interior, closure, the
// subspace topology, the Hausdorff property — are defined apart from
// the laws that use them.

package topological_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The structure and its axioms
// ---------------------------------------------------------------------------

// IsTopology — a topology on a type A is a family T of subsets of A
// closed under the intersection of two members and under the union of
// any subfamily. One component, the family itself, and no carrier: the
// points of the space are ⋃T, and "u is open" is `u ∈ T`. That the
// space and the empty set are open is what the union axiom says at
// the subfamily T and at ∅ (SpaceOpen, EmptyOpen below).
var IsTopology = isTopologyThm{family.DefineStructure(registry.DefEntry{
	Name:    "IsTopology",
	Key:     "prop_7f06f37d65d8cc59",
	Const:   "is_topology",
	Subject: "T",
	Type:    "set(set(A)) → bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"    is_topology(T) ⇔ (∀u v:set(A). u ∈ T ∧ v ∈ T ⇒ u ∩ v ∈ T) ∧ (∀s:set(set(A)). s ⊆ T ⇒ ⋃s ∈ T)",
	},
	// The mints of the constants the definiens spells: membership,
	// binary intersection, inclusion and the union of a family.
})}

// InterOpen — two open sets meet in an open set.
var InterOpen = interOpenThm{family.Add(registry.ProofEntry{
	Name: "InterOpen",
	Key:  "prop_b895452d8b9f532b",
	Build: IsTopology.Axiom(Statement{
		Binders: "∀u v:set(A).",
		Hypotheses: []string{
			"u ∈ T",
			"v ∈ T",
		},
		Conclusion: "u ∩ v ∈ T",
	}),
})}

// UnionsOpen — the union of any family of open sets is open.
var UnionsOpen = unionsOpenThm{family.Add(registry.ProofEntry{
	Name: "UnionsOpen",
	Key:  "prop_7c76bc37d133eb47",
	Build: IsTopology.Axiom(Statement{
		Binders: "∀s:set(set(A)).",
		Hypotheses: []string{
			"s ⊆ T",
		},
		Conclusion: "⋃s ∈ T",
	}),
})}

// ---------------------------------------------------------------------------
// Instances
// ---------------------------------------------------------------------------

// Discrete — every subset of X open: the family of all subsets of X is
// a topology, at every X. Membership in the family is inclusion in X,
// so both obligations are set-theoretic.
var Discrete = discreteThm{family.Add(registry.ProofEntry{
	Name: "Discrete",
	Key:  "prop_edc7603a6948def6",
	Build: family.Instance(IsTopology, "∀X:set(A). is_topology({t:set(A) | t ⊆ X})",
		Case(
			"two subsets of X meet inside X",
			BySets()),
		Case(
			"subsets of X unite inside X",
			BySets()),
	),
})}

// IntersTopologies — the intersection of a family of topologies is a
// topology. A set lies in ⋂F exactly when it lies in every member of F,
// so two such sets meet in a set every member holds, each member being
// closed under the meet, and a family of such sets lies inside every
// member and unites to a set every member holds, each member being
// closed under unions. The family need not be non-empty: the
// intersection of no topologies is the family of all sets, which is
// closed under both.
var IntersTopologies = intersTopologiesThm{family.Add(registry.ProofEntry{
	Name: "IntersTopologies",
	Key:  "prop_c9e98d8c28288dcb",
	Build: family.Theorem(Statement{
		Binders: "∀F:set(set(set(A))).",
		Hypotheses: []string{
			"∀T:set(set(A)). T ∈ F ⇒ is_topology(T)",
		},
		Conclusion: "is_topology(⋂F)",
	},
		func(a *Argument, F *Expr[Set[Set[Set[A]]]], topologies Fact) {
			a.Do(Simp(Fwd(IsTopology)), SplitConj(
				Case(
					"every member of F holds the meet of two sets that all its members hold",
					By(topologies, InterOpen, set_basic.InInters)),
				Case(
					"every member of F holds the union of a family that lies inside all its members",
					By(topologies, UnionsOpen, set_basic.InInters, set_order.SubsetInters)),
			))
		}),
})}

// ---------------------------------------------------------------------------
// What the axioms say about open sets
// ---------------------------------------------------------------------------

// SpaceOpen — the space itself is open: it is the union of the whole
// family, and the whole family is a subfamily of itself.
var SpaceOpen = spaceOpenThm{family.Add(registry.ProofEntry{
	Name: "SpaceOpen",
	Key:  "prop_5579813f541ea260",
	Build: IsTopology.Law("⋃T ∈ T",
		func(a *Argument, T *Expr[Set[Set[A]]], topology IsTopologyFact[on.T]) {
			a.Show(
				"the union axiom at the whole family, which includes itself",
				By(UnionsOpen, At(set_order.SubsetRefl, T), topology))
		}),
})}

// EmptyOpen — the empty set is open: it is the union of the empty
// subfamily, and the empty family is a subfamily of any family.
var EmptyOpen = emptyOpenThm{family.Add(registry.ProofEntry{
	Name: "EmptyOpen",
	Key:  "prop_f167138d96d767d2",
	Build: IsTopology.Law("∅ ∈ T",
		func(a *Argument, T *Expr[Set[Set[A]]], topology IsTopologyFact[on.T]) {
			unitesEmpty := a.Have(
				"the union axiom at the empty subfamily",
				"⋃∅ ∈ T",
				By(UnionsOpen, At(set_order.EmptySubset, T), topology))
			a.Show(
				"and the empty family unites to the empty set",
				By(unitesEmpty, set_algebra.UnionsEmpty))
		}),
})}

// UnionOpen — two open sets unite to an open set: the two form a
// subfamily, whose union the union axiom makes open, and the union of
// a pair is the binary union. The pair's inclusion in T is read by the
// algebra of insert rather than by the set closer, which cannot put
// two SETS into a family (an equation between sets reaches it only
// pointwise).
var UnionOpen = unionOpenThm{family.Add(registry.ProofEntry{
	Name: "UnionOpen",
	Key:  "prop_357af84eeceec992",
	Build: IsTopology.Law(Statement{
		Binders: "∀u v:set(A).",
		Hypotheses: []string{
			"u ∈ T",
			"v ∈ T",
		},
		Conclusion: "u ∪ v ∈ T",
	},
		func(a *Argument, topology IsTopologyFact[on.T], u, v *Member[Set[A], on.T]) {
			pair := a.Have(
				"the two sets form a subfamily: a pair is included when both members are",
				"{u, v} ⊆ T",
				// Pinned at the family instance: Go's Simp does not adapt a
				// rule's type letters to a goal over sets of sets.
				Simp(Fwd(set_order.InsertSubset.Inst[Set[A]]()), Fwd(set_order.EmptySubset.Inst[Set[A]]())),
				By(u, v))
			unitesPair := a.Have(
				"the union axiom at the pair",
				"⋃{u, v} ∈ T",
				By(UnionsOpen, pair, topology))
			a.Show(
				"and the pair unites to the binary union",
				By(unitesPair, set_algebra.UnionsPair))
		}),
})}

// IntersOpen — finitely many open sets meet in an open set, provided
// there is at least one: the intersection of none is the whole type.
// The pairwise axiom reaches every finite family by induction on the
// family. The empty family is not in question; a family enlarged by one
// open set x is either {x}, whose intersection is x, or x beside a
// non-empty family whose intersection the induction hypothesis makes
// open, and the axiom meets the two.
var IntersOpen = intersOpenThm{family.Add(registry.ProofEntry{
	Name: "IntersOpen",
	Key:  "prop_3d6a2c72f87baaa",
	Build: IsTopology.Law(Statement{
		Binders: "∀f:set(set(A)).",
		Hypotheses: []string{
			"finite(f)",
			"¬(f = ∅)",
			"f ⊆ T",
		},
		Conclusion: "⋂f ∈ T",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology IsTopologyFact[on.T],
			f *Expr[Set[Set[A]]],
			finite, nonempty, open Fact,
		) {
			a.Show(
				"the induction carries the property to f, which is finite, non-empty and open throughout",
				ByInduction(finite_set.FiniteInduct, finite, Generalizing(nonempty, open),
					Case(
						"at ∅ there is no family to meet, and the property asks about none",
						Basic()),
					Case(
						"one more open set meets the intersection of those already there",
						Derive(func(b *Argument) {
							x, u := b.FixAs[Set[A]](), b.FixAs[Set[Set[A]]]("u")
							carried := b.Assume() // the induction hypothesis, itself conditional
							given := b.Assume()   // the enlarged family is non-empty and open throughout

							open := b.Have(
								"the new member and those already there are open",
								"x ∈ T ∧ u ⊆ T",
								By(given, set_order.InsertSubset.At(u, T, x)))

							nonEmpty := b.Unless(
								b.Term("u = ∅"),
								"when the new member stands alone, the family is {x}",
								Given(func(c *Argument, alone Fact) {
									c.Show(
										"and its intersection is x, which is open",
										By(alone, open, set_algebra.IntersSing.At(x)))
								}))

							inner := b.Have(
								"so the induction hypothesis makes the rest meet in an open set",
								"⋂u ∈ T",
								By(carried, nonEmpty, open))

							b.Show(
								"and the new member meets that open set in an open set",
								By(
									topology,
									inner,
									open,
									InterOpen.At(T, x, b.TermAs[Set[A]]("⋂u")),
									set_algebra.IntersInsert.At(u, x)))
						}))))
		}),
})}

// OpenPointwise — the pointwise criterion for openness: a set is open
// exactly when each of its points lies in an open set inside it.
// Forward, the set itself is that open set, at every point. Backward,
// the set is then its own interior — a point of it lies in an open set
// inside it, which is what lying in the interior says — and the
// interior is open.
var OpenPointwise = openPointwiseThm{family.Add(registry.ProofEntry{
	Name: "OpenPointwise",
	Key:  "prop_b468e7265e4723a1",
	Build: IsTopology.Law("∀u:set(A). u ∈ T ⇔ (∀x:A. x ∈ u ⇒ ∃v:set(A). v ∈ T ∧ v ⊆ u ∧ x ∈ v)",
		func(a *Argument, T *Expr[Set[Set[A]]], topology IsTopologyFact[on.T], u *Expr[Set[A]]) {
			a.Iff()

			a.Forward(
				"an open set is its own open neighbourhood inside itself, at each of its points",
				func(b *Argument, uOpen Fact) {
					b.Fix("x")
					xIn := b.Assume()
					b.Take(u)
					b.Show(
						"u is open, lies inside itself and holds x",
						By(uOpen, At(set_order.SubsetRefl, u), xIn))
				})

			a.Backward(
				"a set each of whose points lies in an open set inside it is its own interior, which is open",
				func(b *Argument, pointwise Fact) {
					ownInterior := b.Have(
						"a point of u lies in an open set inside u, which is to say in the interior of u, and conversely",
						"u = interior(u)",
						BySets(pointwise, At(InteriorPointwise, T, u)))
					interiorOpen := b.Have(
						"the interior of u is open",
						"interior(u) ∈ T",
						By(InteriorOpen, topology))
					b.Show(
						"so u is open",
						By(Normalized, ownInterior, interiorOpen))
				})
		}),
})}

// SeparatedFromFiniteUnion — a point with an open neighbourhood disjoint
// from each of finitely many sets has one disjoint from their union: the
// intersection of the finitely many separating neighbourhoods. By
// induction on the family. At the empty family the whole space serves.
// Across insert(v, e), the neighbourhood separating x from the new
// member v meets the one the induction hypothesis gives for the rest e.
// The point x is in the space throughout, which is what the empty family
// needs. This is the lemma behind "a compact set in a Hausdorff space is
// closed".
var SeparatedFromFiniteUnion = separatedFromFiniteUnionThm{family.Add(registry.ProofEntry{
	Name: "SeparatedFromFiniteUnion",
	Key:  "prop_1d3e2e910d97e166",
	Build: IsTopology.Law(Statement{
		Binders: "∀x:A. ∀d:set(set(A)).",
		Hypotheses: []string{
			"x ∈ ⋃T",
			"finite(d)",
			"∀v:set(A). v ∈ d ⇒ ∃u:set(A). u ∈ T ∧ x ∈ u ∧ u ∩ v = ∅",
		},
		Conclusion: "∃u:set(A). u ∈ T ∧ x ∈ u ∧ u ∩ ⋃d = ∅",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology IsTopologyFact[on.T],
			x *Expr[A],
			d *Expr[Set[Set[A]]],
			inSpace, finite, separatedMembers Fact,
		) {
			a.Show(
				"the induction carries the property to d, which is finite and separated from x member by member",
				ByInduction(finite_set.FiniteInduct, finite, Generalizing(separatedMembers),
					Case(
						"at ∅ the whole space serves: it is open, contains x, and the empty family unites to nothing",
						Derive(func(b *Argument) {
							b.Assume() // every member of ∅ is separated from x, vacuously
							b.Take(b.Term("⋃T"))
							b.Show(
								"⋃T is open by the union axiom, contains x, and meets ⋃∅ = ∅ in nothing",
								By(Normalized, topology, inSpace, SpaceOpen, set_algebra.UnionsEmpty, set_algebra.InterEmpty))
						})),
					Case(
						"one more set v: the neighbourhood separating x from v meets the one separating x from the rest e",
						Derive(func(b *Argument) {
							v := b.Fix("v")
							b.Fix("e")
							carried := b.Assume()      // the induction hypothesis: e separated member by member ⇒ e separated
							separatedAll := b.Assume() // every member of insert(v, e) is separated from x

							u2, u2Separates := b.Obtain(
								"v is a member of insert(v, e), so some open u₂ ∋ x misses v",
								"∃u₂:set(A). u₂ ∈ T ∧ x ∈ u₂ ∧ u₂ ∩ v = ∅",
								BySets(separatedAll.At(v)))
							rest := b.Have(
								"and e is a subfamily of insert(v, e), so its members are separated from x too",
								"∀w:set(A). w ∈ e ⇒ ∃u:set(A). u ∈ T ∧ x ∈ u ∧ u ∩ w = ∅",
								BySets(separatedAll))
							u1, u1Separates := b.Obtain(
								"hence, by the induction hypothesis, some open u₁ ∋ x misses ⋃e",
								"∃u₁:set(A). u₁ ∈ T ∧ x ∈ u₁ ∧ u₁ ∩ ⋃e = ∅",
								By(carried, rest))

							b.Take(b.Term("u₁ ∩ u₂"))
							b.Show(
								"u₁ ∩ u₂ is open, contains x, and misses every member "+
									"of insert(v, e): v through u₂, the rest through u₁",
								BySets(topology, u1Separates, u2Separates, At(InterOpen, T, u1, u2)))
						}))))
		}),
})}

// ---------------------------------------------------------------------------
// The discrete topology, read
// ---------------------------------------------------------------------------

// DiscreteSpace — the points of the discrete topology on X are the
// points of X: X is one of its own subsets, and every subset lies in X.
var DiscreteSpace = discreteSpaceThm{family.Add(registry.ProofEntry{
	Name: "DiscreteSpace",
	Key:  "prop_3e1bdb14b387a910",
	Build: family.Theorem("∀X:set(A). ⋃{t:set(A) | t ⊆ X} = X",
		func(a *Argument, X *Expr[Set[A]]) {
			a.Show(
				"a point of a subset of X is a point of X, and a point of X is a point of the subset X",
				BySets())
		}),
})}
