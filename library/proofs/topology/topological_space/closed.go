// closed.go — closed sets, the complements in the space of open sets:
// the duality itself, which needs no axiom, and what the axioms make of
// closed sets.

package topological_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Closed sets
// ---------------------------------------------------------------------------

// SpaceClosed — the space is closed: it lies in itself, and its
// complement in itself is the empty set, which is open.
var SpaceClosed = spaceClosedThm{family.Add(registry.ProofEntry{
	Name: "SpaceClosed",
	Key:  "prop_e157a2e02c8f3214",
	Build: IsTopology.Law("closed_in(⋃T)",
		func(a *Argument, topology IsTopologyFact[on.T]) {
			a.Show(
				"the space lies in itself, and removing it from itself leaves the empty set, which is open",
				Unfold(ClosedInDef),
				Simp(Fwd(set_algebra.DiffEqEmpty)),
				By(EmptyOpen, At(set_order.SubsetRefl, a.Term("⋃T")), topology))
		}),
})}

// EmptyClosed — the empty set is closed: it lies in the space, and its
// complement in the space is the space, which is open.
var EmptyClosed = emptyClosedThm{family.Add(registry.ProofEntry{
	Name: "EmptyClosed",
	Key:  "prop_54ca194e94b38437",
	Build: IsTopology.Law("closed_in(∅)",
		func(a *Argument, topology IsTopologyFact[on.T]) {
			a.Show(
				"the empty set lies in the space, and removing "+
					"nothing from the space leaves the space, which is open",
				Unfold(ClosedInDef),
				Simp(Fwd(set_algebra.DiffEmpty)),
				By(SpaceOpen, At(set_order.EmptySubset, a.Term("⋃T")), topology))
		}),
})}

// OpenClosedComplement — a set is open iff it lies in the space and its
// complement in the space is closed: the duality between open and
// closed sets, read in both directions. Closedness of ⋃T ∖ u asks that it
// lie in the space, which any part of ⋃T does, and that its own
// complement ⋃T ∖ (⋃T ∖ u) be open; for u inside the space the double
// complement is u itself, so that clause says exactly that u is open.
// Nothing is asked of T beyond being a family of sets, so the topology
// is spelled.
var OpenClosedComplement = openClosedComplementThm{family.Add(registry.ProofEntry{
	Name: "OpenClosedComplement",
	Key:  "prop_28bbdc01574135f2",
	Build: family.Theorem("∀T:set(set(A)). ∀u:set(A). u ∈ T ⇔ u ⊆ ⋃T ∧ closed_in(T, ⋃T ∖ u)",
		func(a *Argument, T *Expr[Set[Set[A]]], u *Expr[Set[A]]) {
			// A closed set lies in the space with an open complement there;
			// unfolding asks both of ⋃T ∖ u.
			a.Do(Unfold(ClosedInDef))
			a.Iff()

			a.Forward(
				"an open set lies in the space, and its complement there "+
					"is closed, its own complement being the open set itself",
				func(b *Argument, uOpen Fact) {
					within := b.Have(
						"an open set lies in the space, the union of the whole family",
						"u ⊆ ⋃T",
						By(uOpen, set_order.MemberSubsetUnions))
					twice := b.Have(
						"so taking its complement in the space twice returns it",
						"⋃T ∖ (⋃T ∖ u) = u",
						BySets(within))
					b.Do(twice.Rw())
					b.Show(
						"hence ⋃T ∖ u lies in the space, and its complement there is u, which is open",
						By(uOpen, within, At(set_order.SubsetDiff, b.Term("⋃T"), u)))
				})

			a.Backward(
				"a set inside the space whose complement there is "+
					"closed is open, being that complement's own complement",
				func(b *Argument, closed Fact) {
					twice := b.Have(
						"u lies in the space, so taking its complement there twice returns it",
						"⋃T ∖ (⋃T ∖ u) = u",
						BySets(closed))
					b.Show(
						"and the complement of the closed set ⋃T ∖ u is open, which is to say u is",
						By(Normalized, twice, closed))
				})
		}),
})}

// UnionClosed — two closed sets unite to a closed set. The union lies
// in the space because each set does. Its complement in the space is
// open by de Morgan: a point of the space outside the union is outside
// both sets, so the complement of the union is the intersection of the
// two complements, each open because its set is closed, and the
// intersection axiom meets them.
var UnionClosed = unionClosedThm{family.Add(registry.ProofEntry{
	Name: "UnionClosed",
	Key:  "prop_30a882cf96870518",
	Build: IsTopology.Law(Statement{
		Binders: "∀c d:set(A).",
		Hypotheses: []string{
			"closed_in(c)",
			"closed_in(d)",
		},
		Conclusion: "closed_in(c ∪ d)",
	},
		func(a *Argument, topology IsTopologyFact[on.T], c, d *Expr[Set[A]], _ Fact) {
			// A closed set lies in the space with an open complement there.
			// Unfolding asks both of c ∪ d and reads the assumption as four
			// clauses: each set lies in the space, and each complement is
			// open.
			a.Do(Unfold(ClosedInDef))
			cWithin := a.Hyp("c ⊆ ⋃T")
			dWithin := a.Hyp("d ⊆ ⋃T")
			cComplementOpen := a.Hyp("⋃T ∖ c ∈ T")
			dComplementOpen := a.Hyp("⋃T ∖ d ∈ T")

			a.Do(SplitConj(
				Case(
					"the union lies in the space, as each set does",
					By(set_order.UnionSubset, cWithin, dWithin)),
				Case(
					"the complement of c ∪ d in the space is the intersection of the two complements, which is open",
					Derive(func(b *Argument) {
						deMorgan := b.Have(
							"a point of the space is outside c ∪ d exactly when it is outside both",
							"⋃T ∖ (c ∪ d) = (⋃T ∖ c) ∩ (⋃T ∖ d)",
							BySets())
						b.Do(deMorgan.Rw())
						b.Show(
							"and the intersection axiom meets the two open complements",
							By(InterOpen, cComplementOpen, dComplementOpen, topology))
					})),
			))
		}),
})}

// InterClosed — two closed sets meet in a closed set. The meet lies in
// the space because c does. Its complement in the space is open by de
// Morgan: a point of the space outside the meet is outside one of the
// two sets, so the complement of the meet is the union of the two
// complements, each open because its set is closed, and two open sets
// unite to an open set.
var InterClosed = interClosedThm{family.Add(registry.ProofEntry{
	Name: "InterClosed",
	Key:  "prop_c65ea2c662effb2e",
	Build: IsTopology.Law(Statement{
		Binders: "∀c d:set(A).",
		Hypotheses: []string{
			"closed_in(c)",
			"closed_in(d)",
		},
		Conclusion: "closed_in(c ∩ d)",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology IsTopologyFact[on.T],
			c, d *Expr[Set[A]],
			cClosed, dClosed Fact,
		) {
			cParts := a.Conjuncts(
				a.Unfolded(cClosed, ClosedInDef),
				"c lies in the space",
				"the complement of c in the space is open")
			dParts := a.Conjuncts(
				a.Unfolded(dClosed, ClosedInDef),
				"d lies in the space",
				"the complement of d in the space is open")
			deMorgan := a.Have(
				"a point of the space is outside c ∩ d exactly when it is outside one of them",
				"⋃T ∖ (c ∩ d) = (⋃T ∖ c) ∪ (⋃T ∖ d)",
				BySets())
			complementOpen := a.Have(
				"so the complement of c ∩ d in the space is open, a union of two open sets",
				"⋃T ∖ (c ∩ d) ∈ T",
				Derive(func(b *Argument) {
					b.Do(deMorgan.Rw())
					b.Show(
						"two open sets unite to an open set",
						By(UnionOpen.Read(topology), cParts[1], dParts[1]))
				}))
			a.Show(
				"c ∩ d lies in the space, as c does, and its complement there is open",
				BySets(ClosedInDef.At(T, a.TermAs[Set[A]]("c ∩ d")), complementOpen, cParts[0]))
		}),
})}

// IntersClosed — a non-empty family of closed sets meets in a closed
// set. The intersection lies in the space because every member does and
// there is a member — the intersection of no sets is the whole type,
// which is why the family must be non-empty. Its complement in the
// space is open by de Morgan: a point of the space outside the
// intersection is outside some member, so the complement of the
// intersection is the union of the members' complements in the space,
// each open because its member is closed, and the union axiom makes
// that union open.
var IntersClosed = intersClosedThm{family.Add(registry.ProofEntry{
	Name: "IntersClosed",
	Key:  "prop_8ca33fa680e79ba1",
	Build: IsTopology.Law(Statement{
		Binders: "∀f:set(set(A)).",
		Hypotheses: []string{
			"¬(f = ∅)",
			"∀c:set(A). c ∈ f ⇒ closed_in(c)",
		},
		Conclusion: "closed_in(⋂f)",
	},
		func(a *Argument, topology IsTopologyFact[on.T], f *Expr[Set[Set[A]]], _ Fact) {
			// A closed set lies in the space with an open complement there.
			// Unfolding asks both of ⋂f and reads the assumption as two
			// clauses: the family is non-empty, and each member lies in the
			// space with an open complement.
			a.Do(Unfold(ClosedInDef))
			nonEmpty := a.Hyp("¬(f = ∅)")
			closed := a.Hyp("∀c:set(A). c ∈ f ⇒ c ⊆ ⋃T ∧ ⋃T ∖ c ∈ T")

			a.Do(SplitConj(
				Case(
					"the intersection lies in the space, as every member does and there is one",
					Derive(func(b *Argument) {
						within := b.Have(
							"each member of f lies in the space, being closed",
							"∀c:set(A). c ∈ f ⇒ c ⊆ ⋃T",
							By(closed))
						b.Show(
							"so the intersection of the non-empty family f lies in the space",
							By(nonEmpty, within, set_order.IntersSubset))
					})),
				Case(
					"the complement of ⋂f in the space is the union of the members' complements, which is open",
					Derive(func(b *Argument) {
						deMorgan := b.Have(
							"a point of the space is outside ⋂f exactly when it is outside some member",
							"⋃T ∖ ⋂f = ⋃image(λc:set(A). ⋃T ∖ c, f)",
							BySets())
						complement := b.TermAs[Fun[Set[A], Set[A]]]("λc:set(A). ⋃T ∖ c")
						isOpen := b.TermAs[Set[Set[A]]]("λu:set(A). u ∈ T")
						familyOpen := b.Have(
							"the members' complements form a subfamily of T, each member being closed",
							"image(λc:set(A). ⋃T ∖ c, f) ⊆ T",
							// Pinned at the family instance: Go's Simp does not adapt a
							// rule's type letters to a goal over sets of sets.
							Simp(Fwd(set_basic.SubsetDef.Inst[Set[A]]())),
							By(closed, set_image.ForallInImage.At(complement, f, isOpen)))
						b.Do(deMorgan.Rw())
						b.Show(
							"and the union axiom makes their union open",
							By(topology, familyOpen, UnionsOpen))
					})),
			))
		}),
})}

// DiffOpen — an open set with a closed set taken away is open. The open
// set lies in the space, so taking c away from it is meeting it with the
// complement of c in the space, which is open because c is closed; and
// two open sets meet in an open set.
var DiffOpen = diffOpenThm{family.Add(registry.ProofEntry{
	Name: "DiffOpen",
	Key:  "prop_11b47b4a10ebdfb7",
	Build: IsTopology.Law(Statement{
		Binders: "∀u c:set(A).",
		Hypotheses: []string{
			"u ∈ T",
			"closed_in(c)",
		},
		Conclusion: "u ∖ c ∈ T",
	},
		func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			topology IsTopologyFact[on.T],
			u *Member[Set[A], on.T],
			c *Expr[Set[A]],
			cClosed Fact,
		) {
			complement := a.Have(
				"c is closed, so its complement in the space is open",
				"⋃T ∖ c ∈ T",
				By(cClosed, ClosedInDef.At(T, c)))
			meet := a.Have(
				"u lies in the space, so taking c away from it is meeting it with that complement",
				"u ∖ c = u ∩ (⋃T ∖ c)",
				BySets(u))
			a.Do(meet.Rw())
			a.Show(
				"and two open sets meet in an open set",
				By(InterOpen.Read(topology), u, complement))
		}),
})}
